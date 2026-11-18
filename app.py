"""DocToDeck: turn DOCX, PDF, HTML and PPTX files into editable, interactive HTML
presentations, and export ONE self-contained .html file that works offline.

SETUP (Python 3.11+)
    pip install -r requirements.txt
    streamlit run app.py

DEPLOY TO STREAMLIT COMMUNITY CLOUD
    1. Put app.py and requirements.txt in a GitHub repository (public or private).
    2. On share.streamlit.io choose "Create app", pick the repo/branch, set "Main file path" to app.py.
    3. Optional: in "Advanced settings" choose Python 3.11 or newer. No secrets are needed:
       each user types their own AI key in the sidebar, and it stays in their session only.
    Ollama only works when the app runs on the same machine as Ollama (i.e. locally).

ADD AN AI PROVIDER
    Any service with an OpenAI-style /chat/completions endpoint: add one line to PROVIDER_PRESETS
    (name -> (base URL, default model)). Anything else: subclass Provider, implement
    chat(messages, timeout) -> str (return the model's raw text), add its name to PROVIDERS and
    build it in make_provider(). Validation, retries and before/after review are shared.

ARCHITECTURE
    Upload -> Parser -> Deck (single source of truth) -> Renderer -> Preview/Export.
    Every edit (UI or AI) is an EditOp applied by a pure function; undo/redo keeps up to 50 snapshots.
    Sections: 1 schema · 2 edit ops + history · 3 elements + segmentation · 4 format parsers ·
    5 renderer · 6 sample decks · 7 AI engine · 8 quality metrics · 9 Streamlit UI.
"""

import base64
import hashlib
import html as html_lib
import io
import json
import math
import re
import statistics
import time
import zipfile
import xml.etree.ElementTree as ET
from collections import Counter
from dataclasses import dataclass, field
from typing import Annotated, Any, Callable, Literal, Union
from uuid import uuid4

from pydantic import BaseModel, ConfigDict, Field, ValidationError

# ════════════════════════════════════════════════════════════════════════════
# 1. DECK SCHEMA (exactly as specified; extend only via a schema_version bump)
# ════════════════════════════════════════════════════════════════════════════


def _id() -> str:
    return uuid4().hex[:8]


class _Block(BaseModel):
    id: str = Field(default_factory=_id)


class TextBlock(_Block):
    type: Literal["text"] = "text"
    text: str


class BulletsBlock(_Block):
    type: Literal["bullets"] = "bullets"
    items: list[str]
    fragments: bool = False  # reveal items one by one


class ImageBlock(_Block):
    type: Literal["image"] = "image"
    src: str  # data URI
    alt: str = ""
    caption: str = ""


class TableBlock(_Block):
    type: Literal["table"] = "table"
    headers: list[str]
    rows: list[list[str]]


class ChartBlock(_Block):
    type: Literal["chart"] = "chart"
    chart_type: Literal["bar", "line", "pie"]
    labels: list[str]
    series: dict[str, list[float]]
    source_table_id: str | None = None


class CodeBlock(_Block):
    type: Literal["code"] = "code"
    language: str = "python"
    code: str


class QuoteBlock(_Block):
    type: Literal["quote"] = "quote"
    text: str
    source: str = ""


class QuizBlock(_Block):
    type: Literal["quiz"] = "quiz"
    question: str
    options: list[str]
    answer_index: int


Block = Annotated[
    Union[TextBlock, BulletsBlock, ImageBlock, TableBlock, ChartBlock,
          CodeBlock, QuoteBlock, QuizBlock],
    Field(discriminator="type"),
]


class Slide(BaseModel):
    id: str = Field(default_factory=_id)
    title: str = ""
    layout: Literal["title", "section", "title_bullets",
                    "two_column", "image_focus"] = "title_bullets"
    blocks: list[Block] = []
    notes: str = ""
    source_ref: str | None = None  # e.g. "page 3" / "heading 2.1"


class Theme(BaseModel):
    name: str = "clean"
    font_heading: str = "Inter"
    font_body: str = "Inter"
    primary_color: str = "#1F4E79"
    background: str = "#FFFFFF"
    direction: Literal["ltr", "rtl"] = "ltr"


class Deck(BaseModel):
    schema_version: Literal["1.0"] = "1.0"
    title: str
    language: str = "en"
    theme: Theme = Theme()
    transition: Literal["none", "fade", "slide", "convex"] = "slide"
    slides: list[Slide] = []


LAYOUTS = ["title", "section", "title_bullets", "two_column", "image_focus"]
TRANSITIONS = ["none", "fade", "slide", "convex"]
BLOCK_TYPES = ["text", "bullets", "image", "table", "chart", "code", "quote", "quiz"]
MAX_BULLETS = 6
MAX_WORDS = 60

# ════════════════════════════════════════════════════════════════════════════
# 2. EDIT OPERATIONS (shared by UI and AI; the AI never returns a full deck)
# ════════════════════════════════════════════════════════════════════════════


class EditOp(BaseModel):
    op: Literal["update_title", "rewrite_block", "add_block", "delete_block",
                "split_slide", "merge_slides", "move_slide", "delete_slide",
                "change_layout", "set_notes", "table_to_chart", "add_quiz"]
    slide_id: str
    target_id: str | None = None  # block id or second slide id
    payload: dict = {}
    rationale: str = ""  # shown to the user next to the suggestion


class Suggestion(BaseModel):
    summary: str
    ops: list[EditOp]


class OpError(ValueError):
    """Raised when an op cannot be applied to the given deck."""


class _Payload(BaseModel):
    # Extra keys are ignored: small models often add harmless fields.
    model_config = ConfigDict(extra="ignore")


class UpdateTitlePayload(_Payload):
    title: str


class RewriteBlockPayload(_Payload):
    block: Block


class AddBlockPayload(_Payload):
    block: Block
    index: int | None = None


class EmptyPayload(_Payload):
    pass


class SplitSlidePayload(_Payload):
    at_block_index: int
    new_title: str = ""


class MoveSlidePayload(_Payload):
    new_index: int


class ChangeLayoutPayload(_Payload):
    layout: Literal["title", "section", "title_bullets", "two_column", "image_focus"]


class SetNotesPayload(_Payload):
    notes: str


class TableToChartPayload(_Payload):
    chart_type: Literal["bar", "line", "pie"] = "bar"
    label_column: int = 0
    value_columns: list[int] | None = None
    replace_table: bool = False


class AddQuizPayload(_Payload):
    question: str
    options: list[str]
    answer_index: int
    index: int | None = None


def _slide_index(deck: Deck, slide_id: str) -> int:
    for i, s in enumerate(deck.slides):
        if s.id == slide_id:
            return i
    raise OpError(f"slide '{slide_id}' not found")


def _block_index(slide: Slide, block_id: str | None) -> int:
    if not block_id:
        raise OpError("target_id (block id) is required")
    for i, b in enumerate(slide.blocks):
        if b.id == block_id:
            return i
    raise OpError(f"block '{block_id}' not found on slide '{slide.id}'")


def _all_block_ids(deck: Deck) -> set[str]:
    return {b.id for s in deck.slides for b in s.blocks}


def _fresh_block(block: Any, deck: Deck) -> Any:
    """Give a block a new id if its id already exists in the deck."""
    if block.id in _all_block_ids(deck):
        return block.model_copy(update={"id": _id()})
    return block


def _insert_index(index: int | None, length: int) -> int:
    if index is None:
        return length
    return max(0, min(int(index), length))


def parse_number(value: str) -> float | None:
    """Parse '1,234.5', '1 234,5', '45%', '$12' into a float; None if not numeric."""
    s = re.sub(r"[^\d,.\-]", "", str(value).replace(" ", "").replace(" ", ""))
    if not s or not re.search(r"\d", s):
        return None
    if "," in s and "." in s:
        s = s.replace(",", "") if s.rfind(".") > s.rfind(",") else s.replace(".", "").replace(",", ".")
    elif "," in s:
        s = s.replace(",", ".") if re.fullmatch(r"-?\d+,\d{1,2}", s) else s.replace(",", "")
    try:
        return float(s)
    except ValueError:
        return None


def _op_update_title(deck: Deck, op: EditOp, p: UpdateTitlePayload) -> None:
    deck.slides[_slide_index(deck, op.slide_id)].title = p.title.strip()


def _op_rewrite_block(deck: Deck, op: EditOp, p: RewriteBlockPayload) -> None:
    slide = deck.slides[_slide_index(deck, op.slide_id)]
    i = _block_index(slide, op.target_id)
    old, new = slide.blocks[i], p.block.model_copy(update={"id": slide.blocks[i].id})
    if new.type == "image":
        if old.type == "image" and not new.src.startswith("data:image/"):
            new = new.model_copy(update={"src": old.src})  # AI may not touch pixels
        if not new.src.startswith("data:image/"):
            raise OpError("image src must be a data:image/... URI")
    slide.blocks[i] = new


def _op_add_block(deck: Deck, op: EditOp, p: AddBlockPayload) -> None:
    slide = deck.slides[_slide_index(deck, op.slide_id)]
    block = _fresh_block(p.block, deck)
    if block.type == "image" and not block.src.startswith("data:image/"):
        raise OpError("image src must be a data:image/... URI")
    slide.blocks.insert(_insert_index(p.index, len(slide.blocks)), block)


def _op_delete_block(deck: Deck, op: EditOp, p: EmptyPayload) -> None:
    slide = deck.slides[_slide_index(deck, op.slide_id)]
    slide.blocks.pop(_block_index(slide, op.target_id))


def _op_split_slide(deck: Deck, op: EditOp, p: SplitSlidePayload) -> None:
    i = _slide_index(deck, op.slide_id)
    slide = deck.slides[i]
    if not 1 <= p.at_block_index < len(slide.blocks):
        raise OpError(f"at_block_index must be between 1 and {len(slide.blocks) - 1}")
    layout = slide.layout if slide.layout not in ("title", "section") else "title_bullets"
    new = Slide(title=p.new_title.strip() or slide.title, layout=layout,
                blocks=slide.blocks[p.at_block_index:], source_ref=slide.source_ref)
    slide.blocks = slide.blocks[:p.at_block_index]
    deck.slides.insert(i + 1, new)


def _op_merge_slides(deck: Deck, op: EditOp, p: EmptyPayload) -> None:
    i = _slide_index(deck, op.slide_id)
    if not op.target_id or op.target_id == op.slide_id:
        raise OpError("merge_slides needs target_id = id of a different slide")
    j = _slide_index(deck, op.target_id)
    first, second = deck.slides[i], deck.slides[j]
    first.blocks = first.blocks + second.blocks
    first.notes = "\n\n".join(n for n in (first.notes, second.notes) if n.strip())
    deck.slides.pop(j)


def _op_move_slide(deck: Deck, op: EditOp, p: MoveSlidePayload) -> None:
    i = _slide_index(deck, op.slide_id)
    if not 0 <= p.new_index < len(deck.slides):
        raise OpError(f"new_index must be between 0 and {len(deck.slides) - 1}")
    deck.slides.insert(p.new_index, deck.slides.pop(i))


def _op_delete_slide(deck: Deck, op: EditOp, p: EmptyPayload) -> None:
    i = _slide_index(deck, op.slide_id)
    if len(deck.slides) == 1:
        raise OpError("cannot delete the only slide")
    deck.slides.pop(i)


def _op_change_layout(deck: Deck, op: EditOp, p: ChangeLayoutPayload) -> None:
    deck.slides[_slide_index(deck, op.slide_id)].layout = p.layout


def _op_set_notes(deck: Deck, op: EditOp, p: SetNotesPayload) -> None:
    deck.slides[_slide_index(deck, op.slide_id)].notes = p.notes


def _op_table_to_chart(deck: Deck, op: EditOp, p: TableToChartPayload) -> None:
    slide = deck.slides[_slide_index(deck, op.slide_id)]
    i = _block_index(slide, op.target_id)
    table = slide.blocks[i]
    if table.type != "table":
        raise OpError("table_to_chart target must be a table block")
    width = len(table.headers)
    if not table.rows or width < 2 or not 0 <= p.label_column < width:
        raise OpError("table needs at least 2 columns, 1 row and a valid label_column")
    rows = [r + [""] * (width - len(r)) for r in table.rows]
    candidates = p.value_columns if p.value_columns is not None else [
        c for c in range(width) if c != p.label_column]
    series: dict[str, list[float]] = {}
    for c in candidates:
        if not 0 <= c < width or c == p.label_column:
            raise OpError(f"invalid value column {c}")
        values = [parse_number(r[c]) for r in rows]
        if all(v is not None for v in values):
            name = table.headers[c].strip() or f"Series {c + 1}"
            while name in series:
                name += " "
            series[name] = [float(v) for v in values]
    if not series:
        raise OpError("no fully numeric columns to chart")
    chart = ChartBlock(chart_type=p.chart_type, labels=[r[p.label_column] for r in rows],
                       series=series, source_table_id=table.id)
    if p.replace_table:
        slide.blocks[i] = chart
    else:
        slide.blocks.insert(i + 1, chart)


def _op_add_quiz(deck: Deck, op: EditOp, p: AddQuizPayload) -> None:
    slide = deck.slides[_slide_index(deck, op.slide_id)]
    options = [o.strip() for o in p.options if o.strip()]
    if len(options) < 2 or not 0 <= p.answer_index < len(options):
        raise OpError("a quiz needs >= 2 options and a valid answer_index")
    quiz = QuizBlock(question=p.question.strip(), options=options, answer_index=p.answer_index)
    slide.blocks.insert(_insert_index(p.index, len(slide.blocks)), quiz)


OPS: dict[str, tuple[type[_Payload], Callable[[Deck, EditOp, Any], None]]] = {
    "update_title": (UpdateTitlePayload, _op_update_title),
    "rewrite_block": (RewriteBlockPayload, _op_rewrite_block),
    "add_block": (AddBlockPayload, _op_add_block),
    "delete_block": (EmptyPayload, _op_delete_block),
    "split_slide": (SplitSlidePayload, _op_split_slide),
    "merge_slides": (EmptyPayload, _op_merge_slides),
    "move_slide": (MoveSlidePayload, _op_move_slide),
    "delete_slide": (EmptyPayload, _op_delete_slide),
    "change_layout": (ChangeLayoutPayload, _op_change_layout),
    "set_notes": (SetNotesPayload, _op_set_notes),
    "table_to_chart": (TableToChartPayload, _op_table_to_chart),
    "add_quiz": (AddQuizPayload, _op_add_quiz),
}


def apply(deck: Deck, op: EditOp) -> Deck:
    """Pure: return a new Deck with `op` applied; `deck` is never mutated."""
    payload_model, handler = OPS[op.op]
    try:
        payload = payload_model.model_validate(op.payload)
    except ValidationError as exc:
        first = exc.errors()[0]
        where = ".".join(str(x) for x in first.get("loc", ()))
        raise OpError(f"{op.op}: invalid payload at '{where}': {first.get('msg')}") from exc
    new = deck.model_copy(deep=True)  # deepcopy shares immutable strings (cheap images)
    handler(new, op, payload)
    return new


def apply_all(deck: Deck, ops: list[EditOp]) -> Deck:
    for op in ops:
        deck = apply(deck, op)
    return deck


# UI-only actions (kept out of EditOp so the AI contract stays exactly as specified)

def duplicate_slide(deck: Deck, slide_id: str) -> Deck:
    new = deck.model_copy(deep=True)
    i = _slide_index(new, slide_id)
    copy = new.slides[i].model_copy(deep=True)
    copy.id = _id()
    copy.blocks = [b.model_copy(update={"id": _id()}) for b in copy.blocks]
    new.slides.insert(i + 1, copy)
    return new


def add_slide(deck: Deck, after_index: int, title: str = "New slide") -> Deck:
    new = deck.model_copy(deep=True)
    new.slides.insert(_insert_index(after_index + 1, len(new.slides)),
                      Slide(title=title, blocks=[BulletsBlock(items=["First point"])]))
    return new


def update_deck(deck: Deck, **changes: Any) -> Deck:
    """Change deck-level fields (title, language, transition, theme)."""
    new = deck.model_copy(deep=True)
    for key, value in changes.items():
        if key not in Deck.model_fields:
            raise OpError(f"unknown deck field '{key}'")
        setattr(new, key, value)
    return Deck.model_validate(new.model_dump(exclude={"slides"}) | {"slides": []}).model_copy(
        update={"slides": new.slides})


class History:
    """Undo/redo as a list of Deck snapshots (max `limit`). Decks are never mutated."""

    def __init__(self, deck: Deck, limit: int = 50):
        self.present = deck
        self.limit = limit
        self._undo: list[Deck] = []
        self._redo: list[Deck] = []

    def commit(self, deck: Deck) -> bool:
        if deck == self.present:
            return False
        self._undo.append(self.present)
        del self._undo[:-self.limit]
        self._redo.clear()
        self.present = deck
        return True

    @property
    def can_undo(self) -> bool:
        return bool(self._undo)

    @property
    def can_redo(self) -> bool:
        return bool(self._redo)

    def undo(self) -> Deck:
        if self._undo:
            self._redo.append(self.present)
            self.present = self._undo.pop()
        return self.present

    def redo(self) -> Deck:
        if self._redo:
            self._undo.append(self.present)
            self.present = self._redo.pop()
        return self.present


# ════════════════════════════════════════════════════════════════════════════
# 3. PARSING: format-neutral elements + segmentation into slides
# ════════════════════════════════════════════════════════════════════════════
# Parsers emit a flat list of `El` in reading order; `segment()` turns them
# into a Deck. Parsers never render, and the renderer never parses.


@dataclass
class El:
    kind: Literal["title", "subtitle", "heading", "para", "list", "block", "note"]
    text: str = ""
    level: int = 0
    items: list[str] = field(default_factory=list)
    block: Any = None
    ref: str | None = None


@dataclass
class ParseResult:
    deck: Deck
    warnings: list[str]
    seconds: float
    source_text: str


HEAVY_TYPES = {"image", "table", "chart", "code", "quiz"}
TEXT_TYPES = {"text", "bullets", "quote"}
TABLE_ROWS_PER_SLIDE = 8
CODE_LINES_PER_SLIDE = 18
CONTINUED = {"en": "cont.", "fr": "suite", "ar": "تابع"}
_EN_STOP = {"the", "and", "is", "of", "to", "in", "that", "for", "with", "are", "this", "on"}
_FR_STOP = {"le", "la", "les", "des", "est", "et", "une", "pour", "dans", "que", "du", "sur"}


def word_count(text: str) -> int:
    return len(text.split())


def block_text(block: Any) -> str:
    """All human-readable text of a block (used for word counts and coverage)."""
    t = block.type
    if t == "text":
        return block.text
    if t == "bullets":
        return " ".join(block.items)
    if t == "quote":
        return f"{block.text} {block.source}"
    if t == "image":
        return f"{block.alt} {block.caption}"
    if t == "table":
        return " ".join(block.headers + [c for r in block.rows for c in r])
    if t == "chart":
        return " ".join(block.labels + list(block.series))
    if t == "code":
        return block.code
    if t == "quiz":
        return " ".join([block.question] + block.options)
    return ""


def slide_density(slide: Slide) -> tuple[int, int]:
    """(bullet count, words in text-like blocks) — the 6-bullet / 60-word rule."""
    bullets = sum(len(b.items) for b in slide.blocks if b.type == "bullets")
    words = sum(word_count(block_text(b)) for b in slide.blocks if b.type in TEXT_TYPES)
    return bullets, words


def detect_language(text: str) -> str:
    letters = [c for c in text if c.isalpha()]
    if not letters:
        return "en"
    arabic = sum("؀" <= c <= "ۿ" or "ݐ" <= c <= "ݿ" for c in letters)
    if arabic / len(letters) > 0.3:
        return "ar"
    words = re.findall(r"[a-zàâçéèêëîïôûùüÿœ']+", text.lower())
    fr = sum(w in _FR_STOP for w in words)
    en = sum(w in _EN_STOP for w in words)
    return "fr" if fr > en else "en"


def split_sentences(text: str, limit: int = MAX_WORDS) -> list[str]:
    """Split text into sentences; sentences longer than `limit` words are chunked."""
    out: list[str] = []
    for sentence in re.split(r"(?<=[.!?؟…])\s+", text.strip()):
        words = sentence.split()
        while len(words) > limit:
            out.append(" ".join(words[:limit]))
            words = words[limit:]
        if words:
            out.append(" ".join(words))
    return out


def image_to_data_uri(blob: bytes, max_side: int = 1600) -> str | None:
    """Validate image bytes with Pillow and return a browser-safe data URI (or None)."""
    from PIL import Image
    try:
        im = Image.open(io.BytesIO(blob))
        im.load()
    except Exception:
        return None
    fmt = (im.format or "").upper()
    if fmt in {"PNG", "JPEG", "GIF", "WEBP"} and max(im.size) <= max_side:
        mime = "jpeg" if fmt == "JPEG" else fmt.lower()
        return f"data:image/{mime};base64,{base64.b64encode(blob).decode()}"
    im.thumbnail((max_side, max_side))
    buf = io.BytesIO()
    if im.mode in ("RGBA", "LA", "P", "PA"):
        im.convert("RGBA").save(buf, "PNG", optimize=True)
        mime = "png"
    else:
        im.convert("RGB").save(buf, "JPEG", quality=85)
        mime = "jpeg"
    return f"data:image/{mime};base64,{base64.b64encode(buf.getvalue()).decode()}"


def pil_to_data_uri(im: Any) -> str:
    buf = io.BytesIO()
    im.convert("RGB").save(buf, "PNG", optimize=True)
    return f"data:image/png;base64,{base64.b64encode(buf.getvalue()).decode()}"


class _Segmenter:
    """Greedy packer: new slide at H1/H2; continuation slide when limits are hit."""

    def __init__(self, language: str):
        self.slides: list[Slide] = []
        self.cur: Slide | None = None
        self.section = ""
        self.ref: str | None = None
        self.cont = CONTINUED.get(language, CONTINUED["en"])
        self.open_text: str | None = None  # id of the TextBlock receiving sentences
        self.open_list: str | None = None  # id of the BulletsBlock receiving items
        self.orphan_notes: list[str] = []

    def _new(self, title: str, ref: str | None) -> None:
        self.cur = Slide(title=title, source_ref=ref)
        self.slides.append(self.cur)
        self.open_text = self.open_list = None

    def _continue(self, ref: str | None) -> None:
        title = f"{self.section} ({self.cont})" if self.section else ""
        self._new(title, ref or self.ref)

    def _stats(self) -> tuple[int, int, int]:
        bullets, words = slide_density(self.cur) if self.cur else (0, 0)
        heavy = sum(1 for b in self.cur.blocks if b.type in HEAVY_TYPES) if self.cur else 0
        return words, bullets, heavy

    def _ensure(self, words: int, bullets: int = 0, heavy: bool = False, ref: str | None = None) -> None:
        if self.cur is None:
            self._continue(ref)
            return
        w, b, h = self._stats()
        empty = not self.cur.blocks
        too_many_words = w + words > MAX_WORDS and w > 0
        too_many_bullets = b + bullets > MAX_BULLETS and b > 0
        heavy_clash = heavy and (h > 0 or w > 30)
        text_after_heavy = not heavy and h > 0 and w + words > 30
        if not empty and (too_many_words or too_many_bullets or heavy_clash or text_after_heavy):
            self._continue(ref)

    def heading(self, el: El) -> None:
        if el.level <= 2:
            self.section = el.text.strip()
            self.ref = el.ref
            self._new(self.section, el.ref)
        else:
            self.para(El("para", text=el.text, ref=el.ref))
            self.open_text = None

    def para(self, el: El) -> None:
        self.open_list = None
        for sentence in split_sentences(el.text):
            self._ensure(word_count(sentence), ref=el.ref)
            last = self.cur.blocks[-1] if self.cur.blocks else None
            if last is not None and last.id == self.open_text:
                last.text = f"{last.text} {sentence}"
            else:
                block = TextBlock(text=sentence)
                self.cur.blocks.append(block)
                self.open_text = block.id
        self.open_text = None

    def bullets(self, el: El) -> None:
        self.open_text = None
        for item in el.items:
            for chunk in split_sentences(item) if word_count(item) > MAX_WORDS else [item]:
                self._ensure(word_count(chunk), 1, ref=el.ref)
                last = self.cur.blocks[-1] if self.cur.blocks else None
                if last is not None and last.id == self.open_list:
                    last.items.append(chunk)
                else:
                    block = BulletsBlock(items=[chunk])
                    self.cur.blocks.append(block)
                    self.open_list = block.id
        self.open_list = None

    def block(self, el: El) -> None:
        self.open_text = self.open_list = None
        b = el.block
        pieces: list[Any] = [b]
        if b.type == "table" and len(b.rows) > TABLE_ROWS_PER_SLIDE:
            pieces = [TableBlock(headers=b.headers, rows=b.rows[i:i + TABLE_ROWS_PER_SLIDE])
                      for i in range(0, len(b.rows), TABLE_ROWS_PER_SLIDE)]
        elif b.type == "code" and b.code.count("\n") >= CODE_LINES_PER_SLIDE:
            lines = b.code.split("\n")
            pieces = [CodeBlock(language=b.language, code="\n".join(lines[i:i + CODE_LINES_PER_SLIDE]))
                      for i in range(0, len(lines), CODE_LINES_PER_SLIDE)]
        for piece in pieces:
            if piece.type in HEAVY_TYPES:
                self._ensure(0, heavy=True, ref=el.ref)
            else:
                self._ensure(word_count(block_text(piece)), ref=el.ref)
            self.cur.blocks.append(piece)

    def note(self, el: El) -> None:
        if self.cur is None:
            self.orphan_notes.append(el.text)
        else:
            self.cur.notes = f"{self.cur.notes}\n{el.text}".strip()


def _final_layout(slide: Slide) -> str:
    types = [b.type for b in slide.blocks]
    if not types:
        return "section"
    images = types.count("image")
    if images and images == len(types):
        return "image_focus"
    if images or (len(types) >= 2 and any(t in HEAVY_TYPES for t in types)
                  and any(t in TEXT_TYPES for t in types)):
        return "two_column"
    return "title_bullets"


def segment(elements: list[El], title: str) -> Deck:
    """Turn parser elements into a Deck following the slide-segmentation rules."""
    text = " ".join(e.text + " " + " ".join(e.items) for e in elements)
    language = detect_language(text)
    deck_title = next((e.text for e in elements if e.kind == "title" and e.text.strip()), "") or title
    seg = _Segmenter(language)
    subtitles: list[Any] = []
    for i, el in enumerate(elements):
        if el.kind == "title":
            continue
        if (el.kind == "heading" and el.text.strip().lower() == deck_title.strip().lower()
                and i + 1 < len(elements) and elements[i + 1].kind == "heading"):
            continue  # the cover slide already shows this heading
        if el.kind == "subtitle":
            if seg.cur is None:
                subtitles.append(TextBlock(text=el.text))
            else:
                seg.para(el)
        elif el.kind == "heading":
            seg.heading(el)
        elif el.kind == "para":
            seg.para(el)
        elif el.kind == "list":
            seg.bullets(el)
        elif el.kind == "block":
            seg.block(el)
        elif el.kind == "note":
            seg.note(el)
    first_ref = next((e.ref for e in elements if e.ref), None)
    cover = Slide(title=deck_title.strip() or "Untitled", layout="title", blocks=subtitles,
                  notes="\n".join(seg.orphan_notes), source_ref=first_ref)
    body = [s for s in seg.slides if s.blocks or s.title.strip()]
    for s in body:
        s.layout = _final_layout(s)
    theme = Theme(direction="rtl" if language == "ar" else "ltr")
    return Deck(title=cover.title, language=language, theme=theme, slides=[cover] + body)


def elements_text(elements: list[El]) -> str:
    parts = []
    for e in elements:
        parts.append(e.text)
        parts.extend(e.items)
        if e.block is not None:
            parts.append(block_text(e.block))
    return "\n".join(p for p in parts if p)


# ════════════════════════════════════════════════════════════════════════════
# 4. FORMAT PARSERS (DOCX -> PDF -> HTML -> PPTX)
# ════════════════════════════════════════════════════════════════════════════

_W_NS = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
_M_NS = "http://schemas.openxmlformats.org/officeDocument/2006/math"
_HEADING_STYLE = re.compile(r"(heading|titre|überschrift|título|titolo|عنوان)\s*(\d)", re.I)
_MONO_FONT = re.compile(r"courier|mono|consolas|menlo|inconsolata|source code", re.I)
_BULLET_LINE = re.compile(r"^\s*(?:[•●▪■◦‣∙·\-–—*]|\(?\d{1,2}[.)]|\(?[a-zA-Z][.)])\s+")


def _clean_text(text: str) -> str:
    return re.sub(r"\s+", " ", text.replace(" ", " ")).strip()


# ── DOCX ────────────────────────────────────────────────────────────────────

def _docx_footnotes(data: bytes) -> dict[str, str]:
    """python-docx has no footnote API, so read word/footnotes.xml directly."""
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            if "word/footnotes.xml" not in z.namelist():
                return {}
            root = ET.fromstring(z.read("word/footnotes.xml"))
    except (zipfile.BadZipFile, ET.ParseError, KeyError):
        return {}
    notes = {}
    for fn in root.iter(f"{{{_W_NS}}}footnote"):
        if fn.get(f"{{{_W_NS}}}type") in ("separator", "continuationSeparator"):
            continue
        text = _clean_text("".join(t.text or "" for t in fn.iter(f"{{{_W_NS}}}t")))
        if text:
            notes[fn.get(f"{{{_W_NS}}}id", "")] = text
    return notes


def _docx_iter_blocks(parent: Any) -> Any:
    """Yield w:p and w:tbl elements in document order, descending into content controls."""
    for child in parent.iterchildren():
        tag = child.tag.split("}")[-1]
        if tag in ("p", "tbl"):
            yield child
        elif tag in ("sdt", "sdtContent", "customXml"):
            yield from _docx_iter_blocks(child)


def _docx_heading_level(par: Any, base_size: float) -> int:
    from docx.oxml.ns import qn
    name = (par.style.name if par.style is not None else "") or ""
    m = _HEADING_STYLE.search(name)
    if m:
        return int(m.group(2))
    ppr = par._p.pPr
    if ppr is not None:
        outline = ppr.find(qn("w:outlineLvl"))
        if outline is not None and outline.get(qn("w:val"), "").isdigit():
            return min(int(outline.get(qn("w:val"))) + 1, 9)
    text = par.text.strip()
    runs = [r for r in par.runs if r.text.strip()]
    if not runs or word_count(text) > 12 or text.endswith((".", ",", ";")):
        return 0
    sizes = [r.font.size.pt for r in runs if r.font.size is not None]
    size = max(sizes) if sizes else base_size
    if size >= base_size * 1.6:
        return 1
    if size >= base_size * 1.25:
        return 2
    if all(r.bold for r in runs) and word_count(text) <= 8:
        return 3
    return 0


def parse_docx(data: bytes) -> tuple[list[El], str, list[str]]:
    import docx
    from docx.oxml.ns import qn
    from docx.table import Table as DocxTable
    from docx.text.paragraph import Paragraph as DocxParagraph

    document = docx.Document(io.BytesIO(data))
    footnotes = _docx_footnotes(data)
    normal = document.styles["Normal"].font.size if "Normal" in [s.name for s in document.styles] else None
    base_size = normal.pt if normal is not None else 11.0
    els: list[El] = []
    warnings: list[str] = []
    list_buf: list[str] = []
    code_buf: list[str] = []
    section = "start"

    def flush() -> None:
        if list_buf:
            els.append(El("list", items=list_buf.copy(), ref=section))
            list_buf.clear()
        if code_buf:
            els.append(El("block", block=CodeBlock(language="text", code="\n".join(code_buf)), ref=section))
            code_buf.clear()

    for n, elm in enumerate(_docx_iter_blocks(document.element.body), 1):
        if elm.tag == qn("w:tbl"):
            flush()
            table = DocxTable(elm, document)
            rows = [[_clean_text(c.text) for c in r.cells] for r in table.rows]
            rows = [r for r in rows if any(r)]
            if len(rows) >= 2 and max(len(r) for r in rows) >= 2:
                width = max(len(r) for r in rows)
                rows = [r + [""] * (width - len(r)) for r in rows]
                els.append(El("block", block=TableBlock(headers=rows[0], rows=rows[1:]), ref=section))
            else:  # layout table: keep its text
                for r in rows:
                    els.append(El("para", text=" ".join(c for c in r if c), ref=section))
            continue
        par = DocxParagraph(elm, document)
        style = ((par.style.name if par.style is not None else "") or "").lower()
        text = _clean_text(par.text)
        for ref_el in elm.iter(qn("w:footnoteReference")):
            note = footnotes.get(ref_el.get(qn("w:id"), ""))
            if note:
                els.append(El("note", text=note, ref=section))
        for blip in elm.iter(qn("a:blip")):
            part = document.part.related_parts.get(blip.get(qn("r:embed")) or "")
            uri = image_to_data_uri(part.blob) if part is not None else None
            if uri:
                alt = next((d.get("descr", "") for d in elm.iter(qn("wp:docPr"))), "")
                flush()
                els.append(El("block", block=ImageBlock(src=uri, alt=alt or "Image"), ref=section))
            else:
                warnings.append(f"An image near paragraph {n} uses an unsupported format and was skipped.")
        math_nodes = list(elm.iter(f"{{{_M_NS}}}oMath"))
        if math_nodes:
            flush()
            eq = " ".join(_clean_text("".join(t.text or "" for t in m.iter(f"{{{_M_NS}}}t"))) for m in math_nodes)
            els.append(El("block", block=CodeBlock(language="math", code=eq), ref=section))
        if not text:
            continue
        runs = [r for r in par.runs if r.text.strip()]
        is_mono = bool(runs) and all(_MONO_FONT.search(r.font.name or "") for r in runs)
        if style == "title":
            flush()
            els.append(El("title", text=text, ref="title"))
        elif style == "subtitle":
            flush()
            els.append(El("subtitle", text=text, ref="title"))
        elif "code" in style or is_mono:
            if list_buf:
                els.append(El("list", items=list_buf.copy(), ref=section))
                list_buf.clear()
            code_buf.append(par.text.rstrip())
        elif (level := _docx_heading_level(par, base_size)) > 0:
            flush()
            section = f"heading: {text[:50]}"
            els.append(El("heading", text=text, level=level, ref=section))
        elif "list" in style or (par._p.pPr is not None and par._p.pPr.numPr is not None):
            if code_buf:
                flush()
            list_buf.append(text)
        elif "quote" in style or "citation" in style:
            flush()
            els.append(El("block", block=QuoteBlock(text=text), ref=section))
        else:
            flush()
            els.append(El("para", text=text, ref=section))
    flush()
    return els, (document.core_properties.title or "").strip(), warnings


# ── PDF ─────────────────────────────────────────────────────────────────────

_MATH_FONT = re.compile(r"CMMI|CMSY|CMEX|MSAM|MSBM|Math|STIX|Symbol|Euclid|rsfs", re.I)
_PAGE_NUM = re.compile(r"^(page|p\.|seite|página|صفحة)?\s*#(\s*(/|of|sur|de|من)\s*#)?$", re.I)


@dataclass
class _Line:
    text: str
    x0: float
    x1: float
    top: float
    bottom: float
    size: float
    bold: bool
    mono: bool
    math: bool
    col: str = "full"
    block: Any = None  # a ready-made block (table/figure) occupying this position


def _words_to_line(words: list[dict], col: str) -> _Line:
    words = sorted(words, key=lambda w: w["x0"])
    fonts = [w.get("fontname", "") for w in words]
    text = re.sub(r"^\(cid:\d+\)\s*", "• ", " ".join(w["text"] for w in words))  # unmapped bullet glyph
    return _Line(
        text=re.sub(r"\s*\(cid:\d+\)", "", text).strip(),
        x0=min(w["x0"] for w in words), x1=max(w["x1"] for w in words),
        top=min(w["top"] for w in words), bottom=max(w["bottom"] for w in words),
        size=statistics.median(w.get("size", 10) for w in words),
        bold=sum(bool(re.search(r"bold|black|heavy|semibold", f, re.I)) for f in fonts) > len(fonts) / 2,
        mono=all(_MONO_FONT.search(f) for f in fonts),
        math=sum(bool(_MATH_FONT.search(f)) for f in fonts) >= max(1, len(fonts) * 0.3),
        col=col,
    )


def _find_gutter(words: list[dict], width: float) -> float | None:
    """Return the x of a column gutter if words leave a vertical empty band mid-page."""
    rows = len({round(w["top"] / 3) for w in words})
    if len(words) < 40 or rows < 8:
        return None
    coverage = [0] * (int(width) + 2)
    for w in words:
        for x in range(max(0, int(w["x0"])), min(len(coverage), int(w["x1"]) + 1)):
            coverage[x] += 1
    limit = max(1, int(rows * 0.08))
    lo, hi = int(width * 0.3), int(width * 0.7)
    best, run_start, best_len = None, None, 0
    for x in range(lo, hi + 1):
        if coverage[x] <= limit:
            run_start = x if run_start is None else run_start
            if x - run_start + 1 > best_len:
                best_len, best = x - run_start + 1, (run_start + x) / 2
        else:
            run_start = None
    if best is None or best_len < 6:
        return None
    left = sum(1 for w in words if w["x1"] <= best)
    right = sum(1 for w in words if w["x0"] >= best)
    return best if min(left, right) >= len(words) * 0.2 else None


def _page_lines(words: list[dict], width: float, blocks: list[_Line]) -> list[_Line]:
    """Group words into lines and return them in reading order (columns left->right)."""
    gutter = _find_gutter(words, width)
    words = sorted(words, key=lambda w: (w["top"], w["x0"]))
    rows: list[list[dict]] = []
    for w in words:
        if rows and abs(w["top"] - rows[-1][0]["top"]) <= max(2.0, 0.3 * w.get("size", 10)):
            rows[-1].append(w)
        else:
            rows.append([w])
    items: list[_Line] = []
    for row in rows:
        if gutter is None or any(w["x0"] < gutter < w["x1"] for w in row):
            items.append(_words_to_line(row, "full"))
            continue
        left = [w for w in row if w["x1"] <= gutter]
        right = [w for w in row if w["x0"] >= gutter]
        if left:
            items.append(_words_to_line(left, "left"))
        if right:
            items.append(_words_to_line(right, "right"))
    for b in blocks:
        if gutter is not None and not b.x0 < gutter < b.x1:
            b.col = "left" if b.x1 <= gutter else "right"
        items.append(b)
    items.sort(key=lambda ln: ln.top)
    ordered, left_buf, right_buf = [], [], []
    for item in items:
        if item.col == "left":
            left_buf.append(item)
        elif item.col == "right":
            right_buf.append(item)
        else:
            ordered += left_buf + right_buf + [item]
            left_buf, right_buf = [], []
    return ordered + left_buf + right_buf


def _crop(page: Any, bbox: tuple[float, float, float, float], resolution: int = 130) -> str | None:
    x0, top, x1, bottom = bbox
    x0, top = max(page.bbox[0], x0), max(page.bbox[1], top)
    x1, bottom = min(page.bbox[2], x1), min(page.bbox[3], bottom)
    if x1 - x0 < 4 or bottom - top < 4:
        return None
    try:
        return pil_to_data_uri(page.crop((x0, top, x1, bottom)).to_image(resolution=resolution).original)
    except Exception:
        return None


def _inside(w: dict, bbox: tuple[float, float, float, float], pad: float = 1.0) -> bool:
    return (w["x0"] >= bbox[0] - pad and w["x1"] <= bbox[2] + pad
            and w["top"] >= bbox[1] - pad and w["bottom"] <= bbox[3] + pad)


def _pdf_page_content(page: Any, page_no: int) -> tuple[list[_Line], bool]:
    """Return ordered lines (incl. table/figure placeholders) and whether the page looks scanned."""
    area = float(page.width * page.height)
    big_images = [im for im in page.images
                  if (im["x1"] - im["x0"]) * (im["bottom"] - im["top"]) > 0.5 * area]
    if len(page.chars) < 15 and big_images:
        uri = _crop(page, (0, 0, page.width, page.height), resolution=100)
        block = ImageBlock(src=uri, alt=f"Scanned page {page_no}") if uri else None
        return ([_Line("", 0, page.width, 0, page.height, 0, False, False, False, "full", block)]
                if block else []), True
    words = page.extract_words(extra_attrs=["size", "fontname"], keep_blank_chars=False)
    blocks: list[_Line] = []
    taken: list[tuple[float, float, float, float]] = []
    for table in page.find_tables():
        rows = [[_clean_text(c or "") for c in r] for r in table.extract()]
        rows = [r for r in rows if any(r)]
        if len(rows) >= 2 and max(len(r) for r in rows) >= 2:
            width = max(len(r) for r in rows)
            rows = [r + [""] * (width - len(r)) for r in rows]
            x0, top, x1, bottom = table.bbox
            blocks.append(_Line("", x0, x1, top, bottom, 0, False, False, False, "full",
                                TableBlock(headers=rows[0], rows=rows[1:])))
            taken.append(table.bbox)
    figures = [(im["x0"], im["top"], im["x1"], im["bottom"]) for im in page.images
               if im["x1"] - im["x0"] >= 40 and im["bottom"] - im["top"] >= 40]
    if len(page.curves) >= 3:
        cx0 = min(c["x0"] for c in page.curves)
        ctop = min(c["top"] for c in page.curves)
        cx1 = max(c["x1"] for c in page.curves)
        cbot = max(c["bottom"] for c in page.curves)
        inside = sum(1 for w in words if _inside(w, (cx0, ctop, cx1, cbot)))
        if cx1 - cx0 >= 60 and cbot - ctop >= 60 and inside < 0.4 * max(1, len(words)):
            figures.append((cx0 - 4, ctop - 4, cx1 + 4, cbot + 4))
    for bbox in figures:
        if any(_inside({"x0": bbox[0], "x1": bbox[2], "top": bbox[1], "bottom": bbox[3]}, t, 2) for t in taken):
            continue
        label = " ".join(w["text"] for w in words if _inside(w, bbox))
        uri = _crop(page, bbox)
        if uri:
            blocks.append(_Line("", bbox[0], bbox[2], bbox[1], bbox[3], 0, False, False, False, "full",
                                ImageBlock(src=uri, alt=label or f"Figure on page {page_no}")))
            taken.append(bbox)
    free = [w for w in words if not any(_inside(w, t) for t in taken)]
    return _page_lines(free, float(page.width), blocks), False


def parse_pdf(data: bytes) -> tuple[list[El], str, list[str]]:
    import pdfplumber
    warnings: list[str] = []
    pages: list[tuple[list[_Line], float, int]] = []
    scanned = 0
    with pdfplumber.open(io.BytesIO(data)) as pdf:
        title = str((pdf.metadata or {}).get("Title") or "").strip()
        for i, page in enumerate(pdf.pages, 1):
            lines, is_scanned = _pdf_page_content(page, i)
            scanned += is_scanned
            pages.append((lines, float(page.height), i))
    n_pages = len(pages)
    if n_pages and scanned / n_pages >= 0.5:
        warnings.append(f"{scanned} of {n_pages} pages look scanned (no text layer). They were imported "
                        "as page images; text recognition (OCR) is planned for Phase 2.")

    # Repeated headers/footers and page numbers live in the top/bottom margins.
    def norm(t: str) -> str:
        return re.sub(r"\d+", "#", t.lower()).strip()

    margin_counts: Counter = Counter()
    for lines, height, _ in pages:
        seen = {norm(ln.text) for ln in lines
                if ln.block is None and (ln.top < height * 0.09 or ln.bottom > height * 0.91)}
        margin_counts.update(seen)
    repeated = {t for t, c in margin_counts.items() if n_pages >= 2 and c >= max(2, n_pages * 0.5)}
    sizes: Counter = Counter()
    for lines, _, _ in pages:
        for ln in lines:
            if ln.block is None:
                sizes[round(ln.size, 1)] += len(ln.text)
    body = sizes.most_common(1)[0][0] if sizes else 10.0

    els: list[El] = []
    para: list[_Line] = []
    items: list[str] = []
    special: list[_Line] = []
    special_kind = ""
    ref = "page 1"

    def flush_para() -> None:
        if para:
            text = ""
            for ln in para:
                if text.endswith("-") and ln.text[:1].islower():
                    text = text[:-1] + ln.text
                else:
                    text = f"{text} {ln.text}".strip()
            els.append(El("para", text=text, ref=ref))
            para.clear()

    def flush_items() -> None:
        if items:
            els.append(El("list", items=items.copy(), ref=ref))
            items.clear()

    def flush_special(page: Any = None) -> None:
        nonlocal special_kind
        if special and special_kind == "code":
            base = min(ln.x0 for ln in special)
            code = "\n".join(" " * round((ln.x0 - base) / max(1.0, ln.size * 0.6)) + ln.text for ln in special)
            els.append(El("block", block=CodeBlock(language="text", code=code), ref=ref))
        elif special and special_kind == "math" and page is not None:
            bbox = (min(ln.x0 for ln in special) - 3, min(ln.top for ln in special) - 3,
                    max(ln.x1 for ln in special) + 3, max(ln.bottom for ln in special) + 3)
            uri = _crop(page, bbox, resolution=160)
            text = " ".join(ln.text for ln in special)
            if uri:
                els.append(El("block", block=ImageBlock(src=uri, alt=text, caption="Equation"), ref=ref))
            else:
                els.append(El("block", block=CodeBlock(language="math", code=text), ref=ref))
        special.clear()
        special_kind = ""

    def flush_all(page: Any = None) -> None:
        flush_para()
        flush_items()
        flush_special(page)

    with pdfplumber.open(io.BytesIO(data)) as pdf:
        for (lines, height, page_no), page in zip(pages, pdf.pages):
            ref = f"page {page_no}"
            body_lines = [ln for ln in lines if ln.block is not None or not (
                (ln.top < height * 0.09 or ln.bottom > height * 0.91)
                and (norm(ln.text) in repeated or _PAGE_NUM.match(norm(ln.text))))]
            # Footnotes: small-font lines in the lower part of the page, the first one starting with a marker.
            small = sorted((ln for ln in body_lines if ln.block is None and ln.size <= body * 0.88
                            and ln.top > height * 0.7), key=lambda ln: ln.top)
            notes: list[_Line] = []
            if small and re.match(r"^\s*(\d{1,3}|[*†‡§])", small[0].text):
                notes = small
                body_lines = [ln for ln in body_lines if all(ln is not n for n in notes)]
            prev: _Line | None = None
            for ln in body_lines:
                if ln.block is not None:
                    flush_all(page)
                    els.append(El("block", block=ln.block, ref=ref))
                    prev = None
                    continue
                ratio = ln.size / body if body else 1.0
                level = 1 if ratio >= 1.5 else 2 if ratio >= 1.15 else 0
                if not level and ln.bold and word_count(ln.text) <= 10 and not ln.text.endswith((".", ",", ";")):
                    level = 3
                kind = "math" if ln.math else "code" if ln.mono else ""
                if kind:
                    if special_kind != kind:
                        flush_all(page)
                        special_kind = kind
                    special.append(ln)
                    prev = ln
                    continue
                flush_special(page)
                if level:
                    flush_para()
                    flush_items()
                    last = els[-1] if els else None
                    if (last is not None and last.kind == "heading" and last.level == level and prev is not None
                            and ln.top - prev.bottom < ln.size * 0.8):
                        last.text = f"{last.text} {ln.text}"
                    else:
                        els.append(El("heading", text=ln.text, level=level, ref=ref))
                elif _BULLET_LINE.match(ln.text):
                    flush_para()
                    items.append(_BULLET_LINE.sub("", ln.text, count=1))
                elif items and prev is not None and ln.top - prev.bottom < ln.size * 0.6 and ln.x0 > prev.x0 - 1:
                    items[-1] = f"{items[-1]} {ln.text}"
                else:
                    flush_items()
                    new_para = (prev is None or ln.col != prev.col or ln.top - prev.bottom > ln.size * 0.75
                                or abs(ln.size - prev.size) > 0.6)
                    if para and new_para and re.search(r"[.!?:؟]$", para[-1].text):
                        flush_para()
                    para.append(ln)
                prev = ln
            flush_items()
            flush_special(page)  # an open paragraph may continue on the next page
            for ln in notes:
                if re.match(r"^\s*(\d{1,3}|[*†‡§])", ln.text) or not els or els[-1].kind != "note":
                    els.append(El("note", text=ln.text, ref=ref))
                else:
                    els[-1].text = f"{els[-1].text} {ln.text}"
        flush_all()
    return els, title, warnings


# ── HTML ────────────────────────────────────────────────────────────────────

_HTML_TAGS = {"h1", "h2", "h3", "h4", "h5", "h6", "p", "ul", "ol", "li", "table", "thead", "tbody",
              "tfoot", "tr", "th", "td", "img", "figure", "figcaption", "pre", "code", "blockquote",
              "div", "section", "article", "main", "aside", "header", "footer", "span", "a", "b",
              "strong", "i", "em", "u", "br", "hr", "sup", "sub", "small", "mark", "dl", "dt", "dd",
              "caption", "cite", "q", "nav", "html", "body"}
_HTML_DROP = {"script", "style", "noscript", "template", "iframe", "object", "embed", "title",
              "head", "svg", "canvas", "select", "button", "textarea", "frame", "frameset", "math"}


def sanitize_html(raw: str) -> str:
    """nh3 sanitization: scripts, iframes, event handlers and unknown tags are removed."""
    import nh3
    return nh3.clean(raw, tags=_HTML_TAGS, clean_content_tags=_HTML_DROP,
                     attributes={"*": {"class", "role"}, "img": {"src", "alt", "title"},
                                 "td": {"colspan", "rowspan"}, "th": {"colspan", "rowspan"},
                                 "a": {"href"}},
                     url_schemes={"http", "https", "data", "mailto"}, strip_comments=True)


def _is_note(tag: Any) -> bool:
    classes = " ".join(tag.get("class") or []).lower()
    role = (tag.get("role") or "").lower()
    return tag.name == "aside" or "footnote" in classes or "endnote" in classes or role in (
        "doc-footnote", "doc-endnotes", "doc-footnotes")


def parse_html(data: bytes) -> tuple[list[El], str, list[str]]:
    from bs4 import BeautifulSoup, NavigableString, UnicodeDammit
    raw = UnicodeDammit(data, ["utf-8", "windows-1252"]).unicode_markup or ""
    head = BeautifulSoup(raw, "html.parser")  # parsing only; nothing is executed or rendered
    title = _clean_text(head.title.get_text()) if head.title else ""
    soup = BeautifulSoup(sanitize_html(raw), "html.parser")
    els: list[El] = []
    warnings: list[str] = []
    skipped_images = 0

    def image(tag: Any, caption: str = "") -> None:
        nonlocal skipped_images
        src = tag.get("src") or ""
        uri = None
        if src.startswith("data:image/") and ";base64," in src:
            try:
                uri = image_to_data_uri(base64.b64decode(src.split(",", 1)[1]))
            except (ValueError, base64.binascii.Error):
                uri = None
        if uri:
            els.append(El("block", block=ImageBlock(src=uri, alt=tag.get("alt") or "", caption=caption)))
        else:
            skipped_images += 1
            if tag.get("alt"):
                els.append(El("para", text=_clean_text(tag["alt"])))

    def walk(node: Any) -> None:
        for child in node.children:
            if isinstance(child, NavigableString):
                text = _clean_text(str(child))
                if text:
                    els.append(El("para", text=text))
                continue
            name = child.name
            if name == "nav":
                continue
            if _is_note(child):
                text = _clean_text(child.get_text(" "))
                if text:
                    els.append(El("note", text=text))
            elif name in ("h1", "h2", "h3", "h4", "h5", "h6"):
                text = _clean_text(child.get_text(" "))
                if text:
                    els.append(El("heading", text=text, level=int(name[1]), ref=f"heading: {text[:50]}"))
            elif name in ("ul", "ol", "dl"):
                items = []
                for li in child.find_all(["li", "dt", "dd"]):
                    for nested in li.find_all(["ul", "ol"]):
                        nested.extract()
                    text = _clean_text(li.get_text(" "))
                    if text:
                        items.append(text)
                if items:
                    els.append(El("list", items=items))
            elif name == "table":
                rows = [[_clean_text(c.get_text(" ")) for c in tr.find_all(["th", "td"])]
                        for tr in child.find_all("tr")]
                rows = [r for r in rows if any(r)]
                if len(rows) >= 2 and max(len(r) for r in rows) >= 2:
                    width = max(len(r) for r in rows)
                    rows = [r + [""] * (width - len(r)) for r in rows]
                    els.append(El("block", block=TableBlock(headers=rows[0], rows=rows[1:])))
                elif rows:
                    els.append(El("para", text=" ".join(" ".join(r) for r in rows)))
            elif name == "pre":
                code_tag = child.find("code")
                classes = " ".join((code_tag.get("class") if code_tag else child.get("class")) or [])
                lang = re.search(r"(?:language|lang)-([\w+#-]+)", classes)
                els.append(El("block", block=CodeBlock(language=lang.group(1) if lang else "text",
                                                       code=child.get_text().strip("\n"))))
            elif name == "blockquote":
                cite = child.find("cite")
                source = _clean_text(cite.extract().get_text(" ")) if cite else ""
                els.append(El("block", block=QuoteBlock(text=_clean_text(child.get_text(" ")), source=source)))
            elif name == "img":
                image(child)
            elif name == "figure":
                cap = child.find("figcaption")
                caption = _clean_text(cap.extract().get_text(" ")) if cap else ""
                imgs = child.find_all("img")
                for img in imgs:
                    image(img, caption)
                if not imgs and caption:
                    els.append(El("para", text=caption))
            elif name == "p":
                for img in child.find_all("img"):
                    image(img.extract())
                text = _clean_text(child.get_text(" "))
                if text:
                    els.append(El("para", text=text))
            elif name in ("br", "hr"):
                continue
            elif child.find(["p", "h1", "h2", "h3", "h4", "h5", "h6", "ul", "ol", "table", "pre",
                             "blockquote", "img", "figure", "div", "section", "article", "aside"]):
                walk(child)
            else:
                text = _clean_text(child.get_text(" "))
                if text:
                    els.append(El("para", text=text))

    walk(soup)
    merged: list[El] = []
    for el in els:  # inline siblings (text, <b>, <a>) arrive as separate paras: join them
        if (el.kind == "para" and merged and merged[-1].kind == "para"
                and not re.search(r"[.!?:؟]$", merged[-1].text) and word_count(merged[-1].text) < 40):
            merged[-1].text = f"{merged[-1].text} {el.text}"
        else:
            merged.append(el)
    if skipped_images:
        warnings.append(f"{skipped_images} linked image(s) were skipped: only embedded (data URI) images "
                        "can travel inside an offline deck.")
    return merged, title, warnings


# ── PPTX ────────────────────────────────────────────────────────────────────

def _pptx_shapes(shapes: Any) -> Any:
    from pptx.enum.shapes import MSO_SHAPE_TYPE
    for shape in sorted(shapes, key=lambda s: ((s.top or 0), (s.left or 0))):
        if shape.shape_type == MSO_SHAPE_TYPE.GROUP:
            yield from _pptx_shapes(shape.shapes)
        else:
            yield shape


def parse_pptx(data: bytes) -> tuple[list[El], str, list[str]]:
    from pptx import Presentation
    from pptx.enum.shapes import PP_PLACEHOLDER
    prs = Presentation(io.BytesIO(data))
    els: list[El] = []
    warnings: list[str] = []
    deck_title = (prs.core_properties.title or "").strip()
    for n, slide in enumerate(prs.slides, 1):
        ref = f"slide {n}"
        title_shape = slide.shapes.title
        title = _clean_text(title_shape.text_frame.text) if title_shape is not None and title_shape.has_text_frame else ""
        is_cover = n == 1 and title_shape is not None and title_shape.is_placeholder and \
            title_shape.placeholder_format.type == PP_PLACEHOLDER.CENTER_TITLE
        els.append(El("title" if is_cover else "heading", text=title, level=2, ref=ref))
        for shape in _pptx_shapes(slide.shapes):
            if title_shape is not None and shape.shape_id == title_shape.shape_id:
                continue
            if shape.has_chart:
                chart = shape.chart
                plot = chart.plots[0] if len(chart.plots) else None
                if plot is not None:
                    kind = str(chart.chart_type).upper()
                    ctype = "pie" if "PIE" in kind or "DOUGHNUT" in kind else "line" if "LINE" in kind else "bar"
                    series = {(s.name or f"Series {i + 1}"): [float(v or 0) for v in s.values]
                              for i, s in enumerate(plot.series)}
                    els.append(El("block", block=ChartBlock(chart_type=ctype, labels=[str(c) for c in plot.categories],
                                                            series=series), ref=ref))
            elif shape.has_table:
                rows = [[_clean_text(c.text) for c in r.cells] for r in shape.table.rows]
                if len(rows) >= 2:
                    els.append(El("block", block=TableBlock(headers=rows[0], rows=rows[1:]), ref=ref))
            elif hasattr(shape, "image"):
                try:
                    blob = shape.image.blob
                except (AttributeError, ValueError, KeyError):
                    continue
                uri = image_to_data_uri(blob)
                descr = shape._element.xpath("./*[1]/*[local-name()='cNvPr']/@descr")
                if uri:
                    els.append(El("block", block=ImageBlock(src=uri, alt=str(descr[0]) if descr else ""), ref=ref))
                else:
                    warnings.append(f"Slide {n}: an image in an unsupported format was skipped.")
            elif shape.has_text_frame:
                paras = [_clean_text("".join(r.text for r in p.runs) or p.text) for p in shape.text_frame.paragraphs]
                paras = [p for p in paras if p]
                if not paras:
                    continue
                is_sub = shape.is_placeholder and shape.placeholder_format.type == PP_PLACEHOLDER.SUBTITLE
                if is_cover and is_sub:
                    els.extend(El("subtitle", text=p, ref=ref) for p in paras)
                elif len(paras) == 1 and not (shape.is_placeholder and shape.placeholder_format.type == PP_PLACEHOLDER.BODY):
                    els.append(El("para", text=paras[0], ref=ref))
                else:
                    els.append(El("list", items=paras, ref=ref))
        if slide.has_notes_slide:
            notes = slide.notes_slide.notes_text_frame.text.strip() if slide.notes_slide.notes_text_frame else ""
            if notes:
                els.append(El("note", text=notes, ref=ref))
    return els, deck_title, warnings


PARSERS: dict[str, Callable[[bytes], tuple[list[El], str, list[str]]]] = {
    "docx": parse_docx, "pdf": parse_pdf, "html": parse_html, "htm": parse_html, "pptx": parse_pptx,
}


def parse_file(filename: str, data: bytes) -> ParseResult:
    """Parse an uploaded document into a Deck. Raises ValueError with a user-friendly message."""
    ext = filename.rsplit(".", 1)[-1].lower() if "." in filename else ""
    if ext not in PARSERS:
        raise ValueError(f"Unsupported file type '.{ext}'. Use DOCX, PDF, HTML or PPTX.")
    start = time.perf_counter()
    try:
        els, title, warnings = PARSERS[ext](data)
    except (zipfile.BadZipFile, KeyError) as exc:
        raise ValueError(f"This .{ext} file looks damaged or is not a real .{ext} file ({exc}).") from exc
    stem = re.sub(r"[_\-]+", " ", filename.rsplit(".", 1)[0]).strip().title()
    deck = segment(els, title or stem)
    if len(deck.slides) <= 1 and not any(e.kind == "block" for e in els):
        warnings.append("No readable text was found in this file.")
    return ParseResult(deck=deck, warnings=warnings, seconds=time.perf_counter() - start,
                       source_text=elements_text(els))


# ════════════════════════════════════════════════════════════════════════════
# 5. RENDERER: Deck -> one self-contained HTML file (no CDN, works offline)
# ════════════════════════════════════════════════════════════════════════════
# Trade-off: a small built-in slide engine instead of reveal.js keeps every
# export offline-safe and ~1 MB smaller; charts are inline SVG for the same reason.

THEMES: dict[str, dict[str, str]] = {
    "clean": dict(font_heading="Inter", font_body="Inter", primary_color="#1F4E79", background="#FFFFFF"),
    "midnight": dict(font_heading="Inter", font_body="Inter", primary_color="#60A5FA", background="#0F172A"),
    "academic": dict(font_heading="Georgia", font_body="Georgia", primary_color="#7B2D26", background="#FBF8F1"),
    "sunrise": dict(font_heading="Poppins", font_body="Inter", primary_color="#C2410C", background="#FFF7ED"),
    "ocean": dict(font_heading="Inter", font_body="Inter", primary_color="#0E7490", background="#F0F9FF"),
}
_SERIF = {"georgia", "times", "times new roman", "merriweather", "cambria", "garamond", "amiri"}
CHART_PALETTE = ["#E07A1F", "#2E8B57", "#8E44AD", "#C0392B", "#16A085", "#D4AC0D", "#5D6D7E"]
UI_TEXT = {
    "en": dict(correct="Correct!", wrong="Not quite, try again.", notes="Speaker notes",
               no_notes="No notes for this slide.", prev="Previous slide", next="Next slide", slide="Slide"),
    "fr": dict(correct="Bonne réponse !", wrong="Pas tout à fait, réessayez.", notes="Notes de l'orateur",
               no_notes="Pas de notes pour cette diapositive.", prev="Diapositive précédente",
               next="Diapositive suivante", slide="Diapositive"),
    "ar": dict(correct="إجابة صحيحة!", wrong="ليس تماماً، حاول مرة أخرى.", notes="ملاحظات المتحدث",
               no_notes="لا توجد ملاحظات لهذه الشريحة.", prev="الشريحة السابقة", next="الشريحة التالية",
               slide="الشريحة"),
}


def _safe_color(value: str, default: str) -> str:
    return value if re.fullmatch(r"#[0-9a-fA-F]{6}", value or "") else default


def _luminance(hex_color: str) -> float:
    r, g, b = (int(hex_color[i:i + 2], 16) / 255 for i in (1, 3, 5))
    lin = [c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4 for c in (r, g, b)]
    return 0.2126 * lin[0] + 0.7152 * lin[1] + 0.0722 * lin[2]


def _font_stack(font: str, rtl: bool) -> str:
    font = re.sub(r"[^A-Za-z0-9 \-]", "", font or "")[:40].strip()
    serif = font.lower() in _SERIF
    base = ("Georgia, Cambria, 'Times New Roman', serif" if serif else
            "system-ui, -apple-system, 'Segoe UI', Roboto, 'Noto Sans', 'Helvetica Neue', Arial, sans-serif")
    arabic = "'Noto Naskh Arabic', 'Noto Sans Arabic', 'Geeza Pro', 'Segoe UI', Tahoma, " if rtl else ""
    return arabic + (f"'{font}', " if font else "") + base


def theme_css_vars(theme: Theme) -> dict[str, str]:
    default = THEMES["clean"]
    primary = _safe_color(theme.primary_color, default["primary_color"])
    bg = _safe_color(theme.background, default["background"])
    dark = _luminance(bg) < 0.35
    rtl = theme.direction == "rtl"
    return {
        "--primary": primary, "--bg": bg,
        "--on-primary": "#111827" if _luminance(primary) > 0.45 else "#FFFFFF",
        "--text": "#F3F4F6" if dark else "#1F2937", "--muted": "#9CA3AF" if dark else "#6B7280",
        "--line": "rgba(255,255,255,.16)" if dark else "#E5E7EB",
        "--stripe": "rgba(255,255,255,.05)" if dark else "rgba(0,0,0,.035)",
        "--outer": "#000000" if dark else "#D1D5DB",
        "--hfont": _font_stack(theme.font_heading, rtl), "--bfont": _font_stack(theme.font_body, rtl),
    }


def _fmt(v: float) -> str:
    return f"{int(v):,}" if float(v).is_integer() else f"{v:,.2f}".rstrip("0").rstrip(".")


def _nice_step(span: float) -> float:
    raw = span / 5 or 1
    mag = 10 ** math.floor(math.log10(raw))
    return next(m * mag for m in (1, 2, 2.5, 5, 10) if m * mag >= raw)


def chart_svg(block: ChartBlock, primary: str, text: str, muted: str) -> str:
    """Render a ChartBlock as accessible inline SVG (bar, line or pie)."""
    esc = html_lib.escape
    colors = [primary] + [c for c in CHART_PALETTE if c.lower() != primary.lower()]
    width, height = 640, 420
    head = (f'<svg viewBox="0 0 {width} {height}" role="img" xmlns="http://www.w3.org/2000/svg" '
            f'font-family="system-ui, sans-serif" aria-label="{esc(block.chart_type)} chart">')
    series = [(name, vals) for name, vals in block.series.items() if vals]
    labels = block.labels
    if not labels or not series:
        return head + f'<text x="{width / 2}" y="{height / 2}" text-anchor="middle" fill="{muted}">No data</text></svg>'
    parts = [head]
    if block.chart_type == "pie":
        values = [max(0.0, v) for v in series[0][1][:len(labels)]]
        total = sum(values) or 1.0
        cx, cy, r, angle = 190, 210, 175, -math.pi / 2
        for i, (label, value) in enumerate(zip(labels, values)):
            frac, color = value / total, colors[i % len(colors)]
            if frac >= 0.9999:
                parts.append(f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="{color}"><title>{esc(label)}</title></circle>')
            elif frac > 0:
                end = angle + frac * 2 * math.pi
                x1, y1 = cx + r * math.cos(angle), cy + r * math.sin(angle)
                x2, y2 = cx + r * math.cos(end), cy + r * math.sin(end)
                parts.append(f'<path d="M{cx},{cy} L{x1:.1f},{y1:.1f} A{r},{r} 0 {1 if frac > 0.5 else 0} 1 '
                             f'{x2:.1f},{y2:.1f} Z" fill="{color}" stroke="#fff" stroke-width="2">'
                             f'<title>{esc(label)}: {_fmt(value)}</title></path>')
                angle = end
            y = 60 + i * 34
            parts.append(f'<rect x="390" y="{y - 15}" width="18" height="18" rx="3" fill="{color}"/>'
                         f'<text x="416" y="{y}" font-size="22" fill="{text}">{esc(label[:24])} '
                         f'({value / total * 100:.0f}%)</text>')
        return "".join(parts) + "</svg>"
    all_vals = [v for _, vals in series for v in vals[:len(labels)]]
    vmin, vmax = min(0.0, min(all_vals)), max(0.0, max(all_vals))
    if vmax == vmin:
        vmax = vmin + 1
    step = _nice_step(vmax - vmin)
    vmin, vmax = math.floor(vmin / step) * step, math.ceil(vmax / step) * step
    left, right, top, bottom = 70, 16, 50 if len(series) > 1 else 20, 70
    pw, ph = width - left - right, height - top - bottom

    def y_of(v: float) -> float:
        return top + (vmax - v) / (vmax - vmin) * ph

    tick = vmin
    while tick <= vmax + step / 2:
        y = y_of(tick)
        parts.append(f'<line x1="{left}" x2="{width - right}" y1="{y:.1f}" y2="{y:.1f}" stroke="{muted}" '
                     f'stroke-opacity=".3"/><text x="{left - 10}" y="{y + 6:.1f}" text-anchor="end" '
                     f'font-size="20" fill="{muted}">{_fmt(round(tick, 6))}</text>')
        tick += step
    band = pw / len(labels)
    rotate = len(labels) > 6
    for i, label in enumerate(labels):
        x = left + band * (i + 0.5)
        anchor = "end" if rotate else "middle"
        transform = f' transform="rotate(-30 {x:.1f} {height - bottom + 28})"' if rotate else ""
        parts.append(f'<text x="{x:.1f}" y="{height - bottom + 28}" text-anchor="{anchor}" font-size="21" '
                     f'fill="{text}"{transform}>{esc(label[:16])}</text>')
    zero = y_of(0)
    for s_i, (name, vals) in enumerate(series):
        color = colors[s_i % len(colors)]
        vals = vals[:len(labels)]
        if block.chart_type == "bar":
            group = band * 0.72
            bw = group / len(series)
            for i, v in enumerate(vals):
                x = left + band * i + (band - group) / 2 + s_i * bw
                y1, y2 = sorted((y_of(v), zero))
                parts.append(f'<rect x="{x:.1f}" y="{y1:.1f}" width="{bw * 0.92:.1f}" height="{max(1, y2 - y1):.1f}" '
                             f'rx="3" fill="{color}"><title>{esc(name)} · {esc(labels[i])}: {_fmt(v)}</title></rect>')
        else:
            pts = " ".join(f"{left + band * (i + 0.5):.1f},{y_of(v):.1f}" for i, v in enumerate(vals))
            parts.append(f'<polyline points="{pts}" fill="none" stroke="{color}" stroke-width="4" '
                         f'stroke-linejoin="round"/>')
            for i, v in enumerate(vals):
                parts.append(f'<circle cx="{left + band * (i + 0.5):.1f}" cy="{y_of(v):.1f}" r="6" fill="{color}">'
                             f'<title>{esc(name)} · {esc(labels[i])}: {_fmt(v)}</title></circle>')
        if len(series) > 1:
            lx = left + s_i * 150
            parts.append(f'<rect x="{lx}" y="12" width="16" height="16" rx="3" fill="{color}"/>'
                         f'<text x="{lx + 22}" y="27" font-size="19" fill="{text}">{esc(name[:18])}</text>')
    parts.append(f'<line x1="{left}" x2="{width - right}" y1="{zero:.1f}" y2="{zero:.1f}" stroke="{muted}"/>')
    return "".join(parts) + "</svg>"


_DECK_TEMPLATE = r"""<!DOCTYPE html>
<html lang="{{ lang }}" dir="{{ dir }}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="generator" content="DocToDeck">
<title>{{ title }}</title>
<style>
:root{ {% for k, v in vars.items() %}{{ k }}:{{ v | safe }};{% endfor %} }
*{box-sizing:border-box}
html,body{margin:0;height:100%;overflow:hidden;background:var(--outer)}
body{font-family:var(--bfont);color:var(--text)}
.viewport{position:fixed;inset:0;display:flex;align-items:center;justify-content:center}
.deck{position:relative;width:1280px;height:720px;flex:none;transform-origin:center center;perspective:1800px}
.slide{position:absolute;inset:0;padding:52px 72px 56px;background:var(--bg);display:flex;flex-direction:column;
  opacity:0;visibility:hidden;transition:transform .55s ease,opacity .55s ease,visibility .55s;overflow:hidden}
.slide.present{opacity:1;visibility:visible;transform:none;z-index:2}
.t-slide .slide.past{transform:translateX(-100%)} .t-slide .slide.future{transform:translateX(100%)}
[dir=rtl] .t-slide .slide.past{transform:translateX(100%)} [dir=rtl] .t-slide .slide.future{transform:translateX(-100%)}
.t-convex .slide.past{transform:translateX(-60%) rotateY(65deg)} .t-convex .slide.future{transform:translateX(60%) rotateY(-65deg)}
[dir=rtl] .t-convex .slide.past{transform:translateX(60%) rotateY(-65deg)} [dir=rtl] .t-convex .slide.future{transform:translateX(-60%) rotateY(65deg)}
.t-none .slide{transition:none}
@media (prefers-reduced-motion:reduce){.slide,.fragment{transition:none!important}}
.slide-title{font-family:var(--hfont);color:var(--primary);font-size:44px;line-height:1.15;margin:0 0 22px;font-weight:700}
.body{flex:1;min-height:0;display:flex;flex-direction:column;gap:18px;font-size:calc(32px * var(--fit,1));line-height:1.35}
.layout-title{justify-content:center;align-items:center;text-align:center}
.layout-title .slide-title{font-size:64px;margin-bottom:18px}
.layout-title .body{flex:none;align-items:center;color:var(--muted);font-size:calc(30px * var(--fit,1))}
.layout-title .slide-title::after{content:"";display:block;width:120px;height:6px;border-radius:3px;background:var(--primary);margin:26px auto 0}
.layout-section{justify-content:center;background:var(--primary);color:var(--on-primary)}
.layout-section .slide-title{color:var(--on-primary);font-size:60px}
.layout-section .body{flex:none}
.layout-two_column .body{display:grid;grid-template-columns:1fr 1fr;gap:44px;align-items:center}
.col{display:flex;flex-direction:column;gap:18px;min-height:0;min-width:0}
.layout-image_focus .slide-title{font-size:36px;margin-bottom:12px}
.layout-image_focus .body{align-items:center;justify-content:center}
.b-text p{margin:0}
ul.b-bullets{margin:0;padding-inline-start:1.15em}
ul.b-bullets li{margin:.28em 0} ul.b-bullets li::marker{color:var(--primary)}
.fragment{opacity:0;transform:translateY(10px);transition:opacity .35s,transform .35s}
.fragment.visible{opacity:1;transform:none}
figure.b-image{margin:0;display:flex;flex-direction:column;align-items:center;gap:8px;min-height:0}
figure.b-image img{max-width:100%;max-height:430px;object-fit:contain;border-radius:8px}
.layout-image_focus figure.b-image img{height:500px;max-height:none;width:auto;max-width:100%}
figcaption{font-size:.6em;color:var(--muted);text-align:center}
.b-table{overflow:hidden;border-radius:8px}
table{border-collapse:collapse;width:100%;font-size:.7em}
th{background:var(--primary);color:var(--on-primary);text-align:start;padding:9px 12px;font-weight:600}
td{padding:8px 12px;border-bottom:1px solid var(--line);vertical-align:top}
tr:nth-child(even) td{background:var(--stripe)}
pre.b-code{margin:0;background:#0F172A;color:#E2E8F0;padding:20px 24px;border-radius:10px;font-size:.58em;line-height:1.5;
  overflow:hidden;white-space:pre;direction:ltr;text-align:left;font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,'Liberation Mono',monospace}
blockquote.b-quote{margin:0;padding:6px 0;padding-inline-start:28px;border-inline-start:6px solid var(--primary);font-style:italic;font-size:1.05em}
blockquote.b-quote footer{font-style:normal;font-size:.65em;color:var(--muted);margin-top:10px}
.b-chart svg{width:100%;height:auto;max-height:460px;display:block}
.b-quiz .q{font-weight:600;margin-bottom:6px}
.b-quiz button{display:block;width:100%;text-align:start;font:inherit;font-size:.8em;padding:10px 16px;margin:8px 0;color:var(--text);
  background:transparent;border:2px solid var(--line);border-radius:10px;cursor:pointer}
.b-quiz button:hover:not(:disabled){border-color:var(--primary)}
.b-quiz button.correct{border-color:#16A34A;background:rgba(22,163,74,.14)}
.b-quiz button.wrong{border-color:#DC2626;background:rgba(220,38,38,.12)}
.b-quiz .feedback{font-size:.7em;min-height:1.3em;font-weight:600}
button:focus-visible{outline:3px solid var(--primary);outline-offset:2px}
.notes{display:none}
#progress{position:fixed;left:0;bottom:0;height:5px;width:0;background:var(--primary);transition:width .3s;z-index:10}
[dir=rtl] #progress{left:auto;right:0}
.hud{position:fixed;bottom:12px;inset-inline-end:14px;display:flex;gap:6px;align-items:center;z-index:11;font:14px system-ui,sans-serif}
.hud button{border:0;border-radius:14px;padding:4px 11px;background:rgba(0,0,0,.5);color:#fff;cursor:pointer;font:inherit}
.hud .counter{background:rgba(0,0,0,.5);color:#fff;padding:4px 11px;border-radius:14px}
#notes-panel{position:fixed;left:0;right:0;bottom:0;max-height:38%;overflow:auto;background:rgba(15,23,42,.96);color:#F8FAFC;
  padding:14px 24px 40px;font:18px/1.5 system-ui,sans-serif;display:none;z-index:9;white-space:pre-wrap}
#notes-panel strong{display:block;margin-bottom:6px;color:#93C5FD}
body.show-notes #notes-panel{display:block}
{% if preview %}.hud,#progress{display:none}{% endif %}
</style>
</head>
<body class="t-{{ transition }}" data-start="{{ start }}" data-preview="{{ 1 if preview else 0 }}">
<div class="viewport"><div class="deck" id="deck">
{% for s in slides %}
<section class="slide layout-{{ s.layout }}" role="group" aria-roledescription="slide" aria-label="{{ t.slide }} {{ s.number }}">
  {% if s.title %}<h1 class="slide-title" dir="auto">{{ s.title }}</h1>{% endif %}
  <div class="body">
  {% if s.columns %}
    <div class="col">{% for b in s.columns[0] %}{{ b }}{% endfor %}</div>
    <div class="col">{% for b in s.columns[1] %}{{ b }}{% endfor %}</div>
  {% else %}{% for b in s.blocks %}{{ b }}{% endfor %}{% endif %}
  </div>
  <aside class="notes">{{ s.notes }}</aside>
</section>
{% endfor %}
</div></div>
<div id="progress"></div>
<div id="notes-panel" aria-live="polite"><strong>{{ t.notes }}</strong><span></span></div>
<div class="hud"><button type="button" id="btn-prev" aria-label="{{ t.prev }}">{{ '›' if dir == 'rtl' else '‹' }}</button>
<span class="counter" dir="ltr" aria-live="polite"></span>
<button type="button" id="btn-next" aria-label="{{ t.next }}">{{ '‹' if dir == 'rtl' else '›' }}</button>
<button type="button" id="btn-notes" aria-label="{{ t.notes }}">✎</button></div>
<script>
(function () {
  "use strict";
  var body = document.body, deck = document.getElementById("deck");
  var slides = Array.prototype.slice.call(document.querySelectorAll(".slide"));
  var rtl = document.documentElement.dir === "rtl", preview = body.dataset.preview === "1";
  var cur = Math.max(0, Math.min(slides.length - 1, parseInt(body.dataset.start, 10) || 0));
  var noteLabel = {{ t.no_notes | tojson }};
  if (!preview) {
    try { var m = window.location.hash.match(/^#\/(\d+)/); if (m) { cur = Math.max(0, Math.min(slides.length - 1, m[1] - 1)); } } catch (e) {}
  }
  function frags(i) { return slides[i] ? Array.prototype.slice.call(slides[i].querySelectorAll(".fragment")) : []; }
  function fitDeck() {
    var s = Math.min(window.innerWidth / 1280, window.innerHeight / 720);
    deck.style.transform = "scale(" + s + ")";
  }
  function fitText() {
    slides.forEach(function (sl) {
      var b = sl.querySelector(".body"); if (!b) { return; }
      var f = 1; b.style.setProperty("--fit", f);
      while (b.scrollHeight > b.clientHeight + 2 && f > 0.55) { f -= 0.05; b.style.setProperty("--fit", f.toFixed(2)); }
    });
  }
  function update() {
    var counter = document.querySelector(".counter");
    if (counter) { counter.textContent = (cur + 1) + " / " + slides.length; }
    var bar = document.getElementById("progress");
    if (bar) { bar.style.width = (slides.length > 1 ? cur / (slides.length - 1) * 100 : 100) + "%"; }
    var note = slides[cur] ? slides[cur].querySelector(".notes") : null;
    document.querySelector("#notes-panel span").textContent = note && note.textContent.trim() ? note.textContent.trim() : noteLabel;
    if (!preview) { try { history.replaceState(null, "", "#/" + (cur + 1)); } catch (e) {} }
  }
  function show(i, allFragments) {
    cur = i;
    slides.forEach(function (sl, j) {
      sl.classList.toggle("present", j === i); sl.classList.toggle("past", j < i); sl.classList.toggle("future", j > i);
      sl.setAttribute("aria-hidden", j === i ? "false" : "true");
      if (j === i) { sl.removeAttribute("inert"); } else { sl.setAttribute("inert", ""); }
    });
    if (allFragments !== null) { frags(i).forEach(function (f) { f.classList.toggle("visible", allFragments); }); }
    update();
  }
  function next() {
    var hidden = frags(cur).filter(function (f) { return !f.classList.contains("visible"); });
    if (hidden.length) { hidden[0].classList.add("visible"); return; }
    if (cur < slides.length - 1) { show(cur + 1, false); }
  }
  function prev() {
    var shown = frags(cur).filter(function (f) { return f.classList.contains("visible"); });
    if (shown.length) { shown[shown.length - 1].classList.remove("visible"); return; }
    if (cur > 0) { show(cur - 1, true); }
  }
  function toggleFullscreen() {
    try {
      if (document.fullscreenElement) { document.exitFullscreen(); }
      else if (document.documentElement.requestFullscreen) { document.documentElement.requestFullscreen().catch(function () {}); }
    } catch (e) {}
  }
  document.addEventListener("keydown", function (e) {
    var tag = (e.target && e.target.tagName) || "";
    if (tag === "INPUT" || tag === "TEXTAREA" || (tag === "BUTTON" && (e.key === " " || e.key === "Enter"))) { return; }
    if (e.altKey || e.ctrlKey || e.metaKey) { return; }
    var k = e.key;
    if (k === "ArrowRight") { k = rtl ? "back" : "fwd"; } else if (k === "ArrowLeft") { k = rtl ? "fwd" : "back"; }
    if (k === "fwd" || k === "ArrowDown" || k === "PageDown" || k === " " || k === "n") { next(); }
    else if (k === "back" || k === "ArrowUp" || k === "PageUp" || k === "Backspace" || k === "p") { prev(); }
    else if (k === "Home") { show(0, false); } else if (k === "End") { show(slides.length - 1, true); }
    else if (k === "f" || k === "F") { toggleFullscreen(); } else if (k === "s" || k === "S") { body.classList.toggle("show-notes"); }
    else { return; }
    e.preventDefault();
  });
  var touchX = null;
  document.addEventListener("touchstart", function (e) { touchX = e.touches[0].clientX; }, { passive: true });
  document.addEventListener("touchend", function (e) {
    if (touchX === null) { return; }
    var dx = e.changedTouches[0].clientX - touchX; touchX = null;
    if (Math.abs(dx) > 50) { if ((dx < 0) !== rtl) { next(); } else { prev(); } }
  });
  document.getElementById("btn-next").addEventListener("click", next);
  document.getElementById("btn-prev").addEventListener("click", prev);
  document.getElementById("btn-notes").addEventListener("click", function () { body.classList.toggle("show-notes"); });
  Array.prototype.forEach.call(document.querySelectorAll(".b-quiz"), function (q) {
    var fb = q.querySelector(".feedback");
    Array.prototype.forEach.call(q.querySelectorAll("button"), function (btn) {
      btn.addEventListener("click", function () {
        var ok = btn.dataset.correct === "1";
        btn.classList.add(ok ? "correct" : "wrong");
        fb.textContent = ok ? q.dataset.ok : q.dataset.ko;
        if (ok) { Array.prototype.forEach.call(q.querySelectorAll("button"), function (b) { b.disabled = true; }); }
      });
    });
  });
  window.addEventListener("resize", function () { fitDeck(); fitText(); });
  fitDeck();
  show(cur, preview ? true : false);
  fitText();
  window.addEventListener("load", fitText);
})();
</script>
</body>
</html>
"""

_BLOCK_TEMPLATES = {
    "text": '<div class="b-text"><p dir="auto">{{ b.text }}</p></div>',
    "bullets": '<ul class="b-bullets">{% for it in b.items %}<li dir="auto"{% if b.fragments %} class="fragment"{% endif %}>'
               '{{ it }}</li>{% endfor %}</ul>',
    "image": '<figure class="b-image"><img src="{{ src }}" alt="{{ b.alt }}">'
             '{% if b.caption %}<figcaption dir="auto">{{ b.caption }}</figcaption>{% endif %}</figure>',
    "table": '<div class="b-table"><table><thead><tr>{% for h in b.headers %}<th scope="col">{{ h }}</th>{% endfor %}'
             '</tr></thead><tbody>{% for r in b.rows %}<tr>{% for c in r %}<td>{{ c }}</td>{% endfor %}</tr>'
             '{% endfor %}</tbody></table></div>',
    "chart": '<div class="b-chart">{{ svg }}</div>',
    "code": '<pre class="b-code"><code class="language-{{ b.language }}">{{ b.code }}</code></pre>',
    "quote": '<blockquote class="b-quote" dir="auto"><p>{{ b.text }}</p>{% if b.source %}<footer>— {{ b.source }}</footer>'
             '{% endif %}</blockquote>',
    "quiz": '<div class="b-quiz" data-ok="{{ t.correct }}" data-ko="{{ t.wrong }}"><div class="q" dir="auto">{{ b.question }}</div>'
            '{% for o in b.options %}<button type="button" dir="auto" data-correct="{{ 1 if loop.index0 == b.answer_index else 0 }}">'
            '{{ o }}</button>{% endfor %}<div class="feedback" aria-live="polite"></div></div>',
}
_SAFE_IMAGE = re.compile(r"^data:image/(png|jpeg|gif|webp);base64,[A-Za-z0-9+/=\s]+$")
_jinja_cache: dict[str, Any] = {}


def _jinja() -> Any:
    if not _jinja_cache:
        from jinja2 import Environment
        env = Environment(autoescape=True)
        _jinja_cache["deck"] = env.from_string(_DECK_TEMPLATE)
        _jinja_cache.update({k: env.from_string(v) for k, v in _BLOCK_TEMPLATES.items()})
    return _jinja_cache


def _render_block(block: Any, vars_: dict[str, str], t: dict[str, str]) -> str:
    from markupsafe import Markup
    tpl = _jinja()[block.type]
    if block.type == "image":
        # Only raster data URIs are allowed in <img>; anything else becomes an empty pixel.
        src = block.src if _SAFE_IMAGE.match(block.src) else "data:image/gif;base64,R0lGODlhAQABAIAAAAAAAP///yH5BAEAAAAALAAAAAABAAEAAAIBRAA7"
        return tpl.render(b=block, src=src)
    if block.type == "chart":
        return tpl.render(b=block, svg=Markup(chart_svg(block, vars_["--primary"], vars_["--text"], vars_["--muted"])))
    return tpl.render(b=block, t=t)


def _columns(slide: Slide) -> tuple[list[Any], list[Any]]:
    media = [b for b in slide.blocks if b.type in ("image", "chart", "table")]
    other = [b for b in slide.blocks if b.type not in ("image", "chart", "table")]
    if media and other:
        return other, media
    half = (len(slide.blocks) + 1) // 2
    return slide.blocks[:half], slide.blocks[half:]


def render_deck(deck: Deck, start: int = 0, preview: bool = False, only: int | None = None) -> str:
    """Render the deck (or a single slide when `only` is set) as one standalone HTML document."""
    from markupsafe import Markup
    vars_ = theme_css_vars(deck.theme)
    lang = deck.language if deck.language in UI_TEXT else "en"
    t = UI_TEXT[lang]
    chosen = list(enumerate(deck.slides))
    if only is not None and 0 <= only < len(deck.slides):
        chosen = [(only, deck.slides[only])]
    slides = []
    for number, s in chosen:
        if s.layout == "two_column" and len(s.blocks) > 1:
            left, right = _columns(s)
            columns = ([Markup(_render_block(b, vars_, t)) for b in left],
                       [Markup(_render_block(b, vars_, t)) for b in right])
        else:
            columns = None
        slides.append(dict(number=number + 1, title=s.title, layout=s.layout, notes=s.notes, columns=columns,
                           blocks=[Markup(_render_block(b, vars_, t)) for b in s.blocks]))
    return _jinja()["deck"].render(
        lang=re.sub(r"[^A-Za-z\-]", "", deck.language)[:12] or "en", dir=deck.theme.direction, title=deck.title,
        vars=vars_, slides=slides, transition=deck.transition, t=t,
        start=0 if only is not None else max(0, min(start, len(deck.slides) - 1)), preview=preview)


# ════════════════════════════════════════════════════════════════════════════
# 6. SAMPLE DECKS (8 slides, every block type and layout; English + Arabic RTL)
# ════════════════════════════════════════════════════════════════════════════

def _sample_image(label: str) -> str:
    from PIL import Image, ImageDraw
    w, h = 640, 400
    im = Image.new("RGB", (w, h), "#DCEEFB")
    draw = ImageDraw.Draw(im)
    for y in range(h):  # sky-to-sea gradient
        t = y / h
        draw.line([(0, y), (w, y)], fill=(int(220 - 120 * t), int(238 - 90 * t), int(251 - 40 * t)))
    draw.ellipse([470, 40, 570, 140], fill="#FDB813")
    draw.polygon([(0, 400), (180, 190), (330, 400)], fill="#5B7553")
    draw.rectangle([0, 330, w, h], fill="#2E86C1")
    for x in (240, 300, 360):
        draw.ellipse([x, 70, x + 90, 120], fill="#FFFFFF")
    for x in range(250, 440, 22):
        draw.line([(x, 125), (x - 10, 165)], fill="#1B4F72", width=3)
    draw.text((16, 12), label, fill="#1B2631")
    return pil_to_data_uri(im)


def build_sample_deck(arabic: bool = False) -> Deck:
    if arabic:
        tx = dict(
            title="دورة الماء: درس قصير", sub="علوم الصف السادس · مثال من DocToDeck",
            sec="الجزء الأول: كيف يتحرك الماء", stages="المراحل الأربع",
            items=["التبخر: الشمس تسخّن الماء فيتحول إلى بخار", "التكاثف: يبرد البخار فيكوّن السحب",
                   "الهطول: يسقط الماء مطراً أو ثلجاً", "التجمع: يعود الماء إلى الأنهار والبحار"],
            notes="اطلب من الطلاب ذكر مثال من حياتهم اليومية لكل مرحلة.", sun="الشمس محرّك الدورة",
            sun_text="تمدّ الشمس الماء بالطاقة اللازمة للتبخر، بينما تعيد الجاذبية الماء إلى الأرض.",
            alt="رسم توضيحي لجبل وبحر وسحب ومطر", cap="الماء يتحرك بين البحر والسماء واليابسة",
            fig="انظر إلى الصورة", rain="كمية الأمطار الشهرية", month="الشهر", mm="الأمطار (مم)",
            months=["يناير", "فبراير", "مارس", "أبريل"], code="محاكاة بسيطة",
            quote="الماء هو القوة الدافعة للطبيعة كلها.", src="ليوناردو دا فينشي",
            quiz="ما المرحلة التي تتكوّن فيها السحب؟", opts=["التبخر", "التكاثف", "التجمع"], qt="اختبر نفسك")
    else:
        tx = dict(
            title="The Water Cycle: A Short Lesson", sub="Grade 6 Science · DocToDeck sample deck",
            sec="Part 1: How water moves", stages="The four stages",
            items=["Evaporation: the Sun heats water into vapour", "Condensation: vapour cools into clouds",
                   "Precipitation: water falls as rain or snow", "Collection: water returns to rivers and seas"],
            notes="Ask students for one everyday example of each stage.", sun="The Sun drives the cycle",
            sun_text="The Sun gives water the energy to evaporate, while gravity brings it back down.",
            alt="Illustration of a mountain, the sea, clouds and rain", cap="Water moves between sea, sky and land",
            fig="Look closely", rain="Monthly rainfall", month="Month", mm="Rainfall (mm)",
            months=["Jan", "Feb", "Mar", "Apr"], code="A tiny simulation",
            quote="Water is the driving force of all nature.", src="Leonardo da Vinci",
            quiz="In which stage do clouds form?", opts=["Evaporation", "Condensation", "Collection"],
            qt="Check yourself")
    image = _sample_image("DocToDeck")
    table = TableBlock(headers=[tx["month"], tx["mm"]],
                       rows=[[m, v] for m, v in zip(tx["months"], ["78", "64", "52", "31"])])
    chart = ChartBlock(chart_type="bar", labels=tx["months"], series={tx["mm"]: [78, 64, 52, 31]},
                       source_table_id=table.id)
    code = ("water = 100  # litres in a lake\nfor day in range(1, 4):\n"
            "    water -= water * 0.05  # 5% evaporates\n    print(day, round(water, 1))")
    slides = [
        Slide(title=tx["title"], layout="title", blocks=[TextBlock(text=tx["sub"])], source_ref="sample"),
        Slide(title=tx["sec"], layout="section", source_ref="sample"),
        Slide(title=tx["stages"], blocks=[BulletsBlock(items=tx["items"], fragments=True)], notes=tx["notes"]),
        Slide(title=tx["sun"], layout="two_column",
              blocks=[TextBlock(text=tx["sun_text"]), ImageBlock(src=image, alt=tx["alt"], caption=tx["cap"])]),
        Slide(title=tx["fig"], layout="image_focus", blocks=[ImageBlock(src=image, alt=tx["alt"])]),
        Slide(title=tx["rain"], layout="two_column", blocks=[table, chart]),
        Slide(title=tx["code"], blocks=[CodeBlock(language="python", code=code),
                                        QuoteBlock(text=tx["quote"], source=tx["src"])]),
        Slide(title=tx["qt"], blocks=[QuizBlock(question=tx["quiz"], options=tx["opts"], answer_index=1)]),
    ]
    theme = Theme(direction="rtl" if arabic else "ltr")
    return Deck(title=tx["title"], language="ar" if arabic else "en", theme=theme, slides=slides)


# ════════════════════════════════════════════════════════════════════════════
# 7. AI SUGGESTION ENGINE (free providers; one slide per request; never silent)
# ════════════════════════════════════════════════════════════════════════════

AI_TIMEOUT = 30
AI_OPS = {"update_title", "rewrite_block", "add_block", "delete_block", "split_slide",
          "change_layout", "set_notes", "table_to_chart", "add_quiz"}
PROVIDER_PRESETS = {  # model names change often; every field stays editable in the sidebar
    "Groq": ("https://api.groq.com/openai/v1", "llama-3.1-8b-instant"),
    "OpenRouter": ("https://openrouter.ai/api/v1", "meta-llama/llama-3.3-70b-instruct:free"),
    "Hugging Face router": ("https://router.huggingface.co/v1", "meta-llama/Llama-3.1-8B-Instruct"),
    "Custom": ("", ""),
}


class AIError(RuntimeError):
    """A provider or validation problem, worded for the end user."""


class Provider:
    name = "base"

    def chat(self, messages: list[dict[str, str]], timeout: int = AI_TIMEOUT) -> str:
        raise NotImplementedError


def _post(url: str, payload: dict, headers: dict[str, str], timeout: int) -> dict:
    import requests
    try:
        resp = requests.post(url, json=payload, headers=headers, timeout=timeout)
    except requests.Timeout as exc:
        raise AIError(f"The AI provider did not answer within {timeout} s.") from exc
    except requests.RequestException as exc:
        raise AIError(f"Could not reach the AI provider ({type(exc).__name__}). Check the URL and your connection.") from exc
    if resp.status_code >= 400:
        detail = re.sub(r"\s+", " ", resp.text)[:240]
        raise AIError(f"The AI provider returned HTTP {resp.status_code}: {detail}")
    try:
        return resp.json()
    except ValueError as exc:
        raise AIError("The AI provider returned a non-JSON response.") from exc


class OllamaProvider(Provider):
    name = "Ollama"

    def __init__(self, base_url: str, model: str):
        self.base_url, self.model = base_url.rstrip("/") or "http://localhost:11434", model or "llama3.2"

    def chat(self, messages: list[dict[str, str]], timeout: int = AI_TIMEOUT) -> str:
        data = _post(f"{self.base_url}/api/chat", {"model": self.model, "messages": messages, "stream": False,
                                                    "format": "json", "options": {"temperature": 0.2}}, {}, timeout)
        return str((data.get("message") or {}).get("content", ""))


class OpenAICompatibleProvider(Provider):
    """Covers Groq, OpenRouter, the Hugging Face router and any /chat/completions endpoint."""
    name = "OpenAI-compatible"

    def __init__(self, base_url: str, api_key: str, model: str):
        self.base_url, self.api_key, self.model = base_url.rstrip("/"), api_key, model
        self.json_mode = True

    def chat(self, messages: list[dict[str, str]], timeout: int = AI_TIMEOUT) -> str:
        if not self.base_url or not self.model:
            raise AIError("Set a base URL and a model name for the OpenAI-compatible provider.")
        headers = {"Authorization": f"Bearer {self.api_key}"} if self.api_key else {}
        body: dict[str, Any] = {"model": self.model, "messages": messages, "temperature": 0.2}
        if self.json_mode:
            body["response_format"] = {"type": "json_object"}
        try:
            data = _post(f"{self.base_url}/chat/completions", body, headers, timeout)
        except AIError as exc:
            if not (self.json_mode and "HTTP 400" in str(exc)):
                raise
            self.json_mode = False  # some free models reject response_format; retry without it
            body.pop("response_format")
            data = _post(f"{self.base_url}/chat/completions", body, headers, timeout)
        try:
            return str(data["choices"][0]["message"]["content"] or "")
        except (KeyError, IndexError, TypeError) as exc:
            raise AIError("Unexpected response shape from the provider.") from exc


class GeminiProvider(Provider):
    name = "Gemini"

    def __init__(self, api_key: str, model: str):
        self.api_key, self.model = api_key, model or "gemini-2.5-flash"

    def chat(self, messages: list[dict[str, str]], timeout: int = AI_TIMEOUT) -> str:
        if not self.api_key:
            raise AIError("Enter a Gemini API key in the sidebar.")
        system = "\n".join(m["content"] for m in messages if m["role"] == "system")
        contents = [{"role": "model" if m["role"] == "assistant" else "user", "parts": [{"text": m["content"]}]}
                    for m in messages if m["role"] != "system"]
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{self.model}:generateContent"
        data = _post(url, {"systemInstruction": {"parts": [{"text": system}]}, "contents": contents,
                           "generationConfig": {"temperature": 0.2, "responseMimeType": "application/json"}},
                     {"x-goog-api-key": self.api_key}, timeout)
        try:
            return "".join(p.get("text", "") for p in data["candidates"][0]["content"]["parts"])
        except (KeyError, IndexError, TypeError) as exc:
            raise AIError("Gemini returned no text (the request may have been blocked).") from exc


SYSTEM_PROMPT = """You improve ONE slide of a teaching presentation for students.
Reply with ONLY a JSON object, no prose, no markdown:
{"summary": "<one short sentence>", "ops": [<op>, ...]}
Each op: {"op": "<name>", "slide_id": "<slide id>", "target_id": "<block id or null>", "payload": {...}, "rationale": "<why, max 15 words>"}
Allowed ops (payload shape):
- update_title: {"title": str}
- rewrite_block (target_id = block id): {"block": BLOCK}
- add_block: {"block": BLOCK, "index": int or null}
- delete_block (target_id = block id): {}
- split_slide: {"at_block_index": int >= 1, "new_title": str}
- change_layout: {"layout": "title"|"section"|"title_bullets"|"two_column"|"image_focus"}
- set_notes: {"notes": str}
- table_to_chart (target_id = table block id): {"chart_type": "bar"|"line"|"pie"}
- add_quiz: {"question": str, "options": [str, str, str], "answer_index": int}
BLOCK is one of:
{"type": "text", "text": str}
{"type": "bullets", "items": [str], "fragments": bool}
{"type": "quote", "text": str, "source": str}
{"type": "code", "language": str, "code": str}
Rules: at most 5 ops; only use ids shown in the slide; write in the slide's language ({language});
max 6 bullets and 60 words per slide; never invent facts; never change images.
Example: {"summary": "Shorter bullets", "ops": [{"op": "rewrite_block", "slide_id": "a1b2c3d4", "target_id": "e5f6a7b8", "payload": {"block": {"type": "bullets", "items": ["Short point one", "Short point two"], "fragments": true}}, "rationale": "Bullets are easier to read than a paragraph"}]}"""


def slide_for_prompt(slide: Slide) -> dict:
    data = slide.model_dump(exclude={"source_ref"})
    for b in data["blocks"]:
        if b["type"] == "image":
            b["src"] = "(image data omitted)"
    return data


def build_messages(deck: Deck, slide_id: str, instruction: str) -> list[dict[str, str]]:
    slide = deck.slides[_slide_index(deck, slide_id)]
    outline = "\n".join(f"{i + 1}. {s.title or '(untitled)'}" for i, s in enumerate(deck.slides))
    user = (f"Deck title: {deck.title}\nDeck outline:\n{outline}\n\nSlide to improve (JSON):\n"
            f"{json.dumps(slide_for_prompt(slide), ensure_ascii=False)}\n\n"
            f"Teacher's request: {instruction.strip() or 'Make this slide clearer and easier to present.'}")
    return [{"role": "system", "content": SYSTEM_PROMPT.replace("{language}", deck.language)},
            {"role": "user", "content": user}]


def extract_json(raw: str) -> Any:
    text = re.sub(r"^```(?:json)?\s*|\s*```$", "", raw.strip(), flags=re.I)
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        start, end = text.find("{"), text.rfind("}")
        if start == -1 or end <= start:
            raise ValueError("the reply contains no JSON object")
        return json.loads(text[start:end + 1])


def validate_suggestion(raw: str, deck: Deck, slide_id: str) -> tuple[Suggestion, Deck]:
    """Parse + validate an AI reply; dry-run every op. Raises ValueError with a precise reason."""
    try:
        data = extract_json(raw)
    except (json.JSONDecodeError, ValueError) as exc:
        raise ValueError(f"invalid JSON: {exc}") from exc
    if isinstance(data, list):
        data = {"summary": "Suggested edits", "ops": data}
    try:
        suggestion = Suggestion.model_validate(data)
    except ValidationError as exc:
        first = exc.errors()[0]
        raise ValueError(f"schema error at {'.'.join(map(str, first['loc']))}: {first['msg']}") from exc
    if not suggestion.ops:
        raise ValueError("'ops' is empty: propose at least one edit")
    if len(suggestion.ops) > 8:
        raise ValueError("too many ops: propose at most 5")
    for op in suggestion.ops:
        if op.op not in AI_OPS:
            raise ValueError(f"op '{op.op}' is not allowed here")
        op.slide_id = slide_id  # one slide per request: a wrong slide id is a harmless slip
    try:
        after = apply_all(deck, suggestion.ops)
    except OpError as exc:
        raise ValueError(f"an op cannot be applied: {exc}") from exc
    return suggestion, after


def request_suggestion(provider: Provider, deck: Deck, slide_id: str, instruction: str = "",
                       retries: int = 2) -> tuple[Suggestion, Deck, int]:
    """Ask the provider for edits to one slide; retry with the validation error appended."""
    messages = build_messages(deck, slide_id, instruction)
    error = ""
    for attempt in range(1, retries + 2):
        raw = provider.chat(messages)
        try:
            suggestion, after = validate_suggestion(raw, deck, slide_id)
            return suggestion, after, attempt
        except ValueError as exc:
            error = str(exc)
            messages = messages + [
                {"role": "assistant", "content": raw[:4000]},
                {"role": "user", "content": f"Your reply was invalid: {error}. Reply again with ONLY the "
                                            "corrected JSON object."}]
    raise AIError(f"The AI gave an invalid answer {retries + 1} times. Last problem: {error}")


# ════════════════════════════════════════════════════════════════════════════
# 8. QUALITY METRICS (measured, not guessed)
# ════════════════════════════════════════════════════════════════════════════

def tokens(text: str) -> list[str]:
    return [w.lower() for w in re.findall(r"[^\W\d_]{2,}", text)]


def deck_text(deck: Deck) -> str:
    parts = [deck.title]
    for s in deck.slides:
        parts += [s.title, s.notes] + [block_text(b) for b in s.blocks]
    return "\n".join(parts)


def coverage(source_text: str, deck: Deck) -> float:
    """Share of source word occurrences that also occur in the deck (multiset match)."""
    src, dst = Counter(tokens(source_text)), Counter(tokens(deck_text(deck)))
    total = sum(src.values())
    return 1.0 if not total else sum(min(c, dst[w]) for w, c in src.items()) / total


def density_ratio(deck: Deck) -> float:
    """Share of slides within the 6-bullet / 60-word limits."""
    if not deck.slides:
        return 1.0
    ok = sum(1 for s in deck.slides if (lambda bw: bw[0] <= MAX_BULLETS and bw[1] <= MAX_WORDS)(slide_density(s)))
    return ok / len(deck.slides)


# ════════════════════════════════════════════════════════════════════════════
# 9. STREAMLIT UI
# ════════════════════════════════════════════════════════════════════════════

import streamlit as st  # noqa: E402  (kept here so sections 1-8 stay importable as a library)

BLOCK_LABEL = {"text": "Text", "bullets": "Bullet list", "image": "Image", "table": "Table", "chart": "Chart",
               "code": "Code", "quote": "Quote", "quiz": "Quiz"}
LAYOUT_LABEL = {"title": "Title slide", "section": "Section divider", "title_bullets": "Title + content",
                "two_column": "Two columns", "image_focus": "Big image"}
LANG_LABEL = {"en": "English", "fr": "Français", "ar": "العربية"}
PROVIDERS = ["Off", "Ollama (local)", "OpenAI-compatible", "Gemini"]
PREVIEW_DATA_URL_LIMIT = 1_500_000  # browsers cap data: URLs around 2 MB


def _ss() -> Any:
    ss = st.session_state
    for key, value in {"hist": None, "cur": 0, "rev": 0, "warnings": [], "parse_info": None, "file_sig": None,
                       "suggestion": None, "flash": [], "export": (None, b""), "ai_provider": "Off",
                       "ai_preset": "Groq", "ai_base_url": PROVIDER_PRESETS["Groq"][0],
                       "ai_model": PROVIDER_PRESETS["Groq"][1], "ai_key": "", "ai_ollama_url": "http://localhost:11434",
                       "ai_ollama_model": "llama3.2", "ai_gemini_key": "", "ai_gemini_model": "gemini-2.5-flash"}.items():
        ss.setdefault(key, value)
    if ss.hist is not None and not isinstance(ss.hist, History):  # app code was reloaded: migrate the deck
        ss.hist = History(Deck.model_validate(ss.hist.present.model_dump()))
    return ss


def _deck() -> Deck | None:
    hist = st.session_state.hist
    return hist.present if hist else None


def _flash(kind: str, message: str) -> None:
    st.session_state.flash.append((kind, message))


def _commit(new: Deck, message: str = "") -> None:
    ss = st.session_state
    if ss.hist.commit(new):
        ss.rev += 1
        if message:
            _flash("success", message)
    ss.cur = max(0, min(ss.cur, len(new.slides) - 1))


def _run(ops: list[EditOp], message: str = "") -> bool:
    try:
        _commit(apply_all(_deck(), ops), message)
        return True
    except OpError as exc:
        _flash("error", f"That change could not be applied: {exc}")
        return False


def _load(deck: Deck, info: dict | None = None, warnings: list[str] | None = None) -> None:
    ss = st.session_state
    ss.hist, ss.cur, ss.suggestion = History(deck), 0, None
    ss.rev += 1
    ss.parse_info, ss.warnings = info, list(warnings or [])


def _iframe(html_doc: str, height: int) -> None:
    """Preview in an iframe. A data: URL gives the preview an opaque origin (isolated from the app)."""
    encoded = html_doc.encode("utf-8")
    if len(encoded) * 4 // 3 < PREVIEW_DATA_URL_LIMIT:
        st.iframe("data:text/html;charset=utf-8;base64," + base64.b64encode(encoded).decode(), height=height)
    else:
        st.iframe(html_doc, height=height)


def _slug(text: str) -> str:
    return re.sub(r"[^\w\-]+", "-", text, flags=re.U).strip("-")[:60] or "presentation"


# ── sidebar callbacks ───────────────────────────────────────────────────────

def _cb_pick(key: str) -> None:
    st.session_state.cur = st.session_state[key]


def _cb_move(delta: int) -> None:
    ss, deck = st.session_state, _deck()
    slide = deck.slides[ss.cur]
    if _run([EditOp(op="move_slide", slide_id=slide.id, payload={"new_index": ss.cur + delta})]):
        ss.cur += delta


def _cb_duplicate() -> None:
    ss, deck = st.session_state, _deck()
    _commit(duplicate_slide(deck, deck.slides[ss.cur].id), "Slide duplicated.")
    ss.cur += 1


def _cb_delete_slide() -> None:
    deck = _deck()
    _run([EditOp(op="delete_slide", slide_id=deck.slides[st.session_state.cur].id)], "Slide deleted (Undo restores it).")


def _cb_add_slide() -> None:
    ss = st.session_state
    _commit(add_slide(_deck(), ss.cur), "New slide added.")
    ss.cur += 1


def _cb_deck_field(key: str, field_name: str) -> None:
    deck, value = _deck(), st.session_state[key]
    theme = deck.theme
    if field_name == "theme":
        _commit(update_deck(deck, theme=Theme(name=value, direction=theme.direction, **THEMES[value])))
    elif field_name == "color":
        _commit(update_deck(deck, theme=theme.model_copy(update={"primary_color": value})))
    elif field_name == "direction":
        _commit(update_deck(deck, theme=theme.model_copy(update={"direction": value})))
    elif field_name == "language":
        _commit(update_deck(deck, language=value,
                            theme=theme.model_copy(update={"direction": "rtl" if value == "ar" else "ltr"})))
    elif field_name == "title":
        _commit(update_deck(deck, title=value.strip() or deck.title))
    else:
        _commit(update_deck(deck, **{field_name: value}))


def _cb_undo() -> None:
    ss = st.session_state
    ss.hist.undo()
    ss.rev += 1
    ss.cur = max(0, min(ss.cur, len(ss.hist.present.slides) - 1))


def _cb_redo() -> None:
    ss = st.session_state
    ss.hist.redo()
    ss.rev += 1
    ss.cur = max(0, min(ss.cur, len(ss.hist.present.slides) - 1))


def _cb_copy(widget_key: str, store_key: str) -> None:
    st.session_state[store_key] = st.session_state[widget_key]


def _cb_preset() -> None:
    ss = st.session_state
    url, model = PROVIDER_PRESETS[ss.w_ai_preset]
    ss.ai_preset = ss.w_ai_preset
    if url:
        ss.ai_base_url = ss.w_ai_base_url = url
        ss.ai_model = ss.w_ai_model = model


def _persist_text(label: str, store_key: str, **kwargs: Any) -> None:
    """A text input whose value survives being hidden (Streamlit drops state of unrendered widgets)."""
    widget_key = f"w_{store_key}"
    if widget_key not in st.session_state:
        st.session_state[widget_key] = st.session_state[store_key]
    st.text_input(label, key=widget_key, on_change=_cb_copy, args=(widget_key, store_key), **kwargs)


def make_provider() -> Provider | None:
    ss = st.session_state
    choice = ss.ai_provider
    if choice == "Ollama (local)":
        return OllamaProvider(ss.ai_ollama_url, ss.ai_ollama_model)
    if choice == "OpenAI-compatible":
        return OpenAICompatibleProvider(ss.ai_base_url, ss.ai_key, ss.ai_model)
    if choice == "Gemini":
        return GeminiProvider(ss.ai_gemini_key, ss.ai_gemini_model)
    return None


# ── sidebar ─────────────────────────────────────────────────────────────────

def _handle_upload(uploaded: Any) -> None:
    ss = st.session_state
    data = uploaded.getvalue()
    sig = hashlib.sha256(data).hexdigest() + uploaded.name
    if sig == ss.file_sig:
        return
    ss.file_sig = sig
    if uploaded.name.lower().endswith(".json"):
        try:
            _load(Deck.model_validate_json(data), {"name": uploaded.name, "seconds": 0.0})
            _flash("success", "Saved deck loaded.")
        except ValidationError as exc:
            _flash("error", f"This JSON file is not a DocToDeck deck ({exc.error_count()} problems found).")
        return
    with st.spinner(f"Reading {uploaded.name}…"):
        try:
            result = parse_file(uploaded.name, data)
        except ValueError as exc:
            _flash("error", str(exc))
            return
        except Exception as exc:  # parser libraries raise many types on malformed files
            _flash("error", f"Sorry, this file could not be read ({type(exc).__name__}). "
                            "Try saving it again from Word/PowerPoint or exporting a fresh PDF.")
            return
    warnings = list(result.warnings)
    if result.seconds > 15:
        warnings.append(f"Parsing took {result.seconds:.1f} s (over the 15 s target).")
    _load(result.deck, {"name": uploaded.name, "seconds": result.seconds,
                        "coverage": coverage(result.source_text, result.deck)}, warnings)
    _flash("success", f"Created {len(result.deck.slides)} slides from {uploaded.name}.")


def sidebar() -> None:
    ss = st.session_state
    st.sidebar.title("🎞️ DocToDeck")
    with st.sidebar:
        st.subheader("1. Upload a file")
        uploaded = st.file_uploader("DOCX, PDF, HTML, PPTX or a saved .json deck",
                                    type=["docx", "pdf", "html", "htm", "pptx", "json"], key="upload")
        if uploaded is not None:
            _handle_upload(uploaded)
        deck = _deck()
        if deck is None:
            st.caption("Or start from a sample:")
            c1, c2 = st.columns(2)
            c1.button("English sample", on_click=lambda: _load(build_sample_deck()), width="stretch")
            c2.button("Arabic sample", on_click=lambda: _load(build_sample_deck(arabic=True)), width="stretch")
            return
        n = len(deck.slides)
        st.subheader("2. Slides")
        with st.container(height=min(320, 46 + 34 * n)):
            key = f"pick_{ss.rev}"
            st.radio("Slides", list(range(n)), index=ss.cur, key=key, label_visibility="collapsed",
                     format_func=lambda i: f"{i + 1}. {(deck.slides[i].title or '(untitled)')[:42]}",
                     on_change=_cb_pick, args=(key,))
        c = st.columns(4)
        c[0].button("↑", help="Move slide up", on_click=_cb_move, args=(-1,), disabled=ss.cur == 0, width="stretch")
        c[1].button("↓", help="Move slide down", on_click=_cb_move, args=(1,), disabled=ss.cur >= n - 1, width="stretch")
        c[2].button("⧉", help="Duplicate slide", on_click=_cb_duplicate, width="stretch")
        c[3].button("🗑", help="Delete slide", on_click=_cb_delete_slide, disabled=n == 1, width="stretch")
        st.button("＋ New slide after this one", on_click=_cb_add_slide, width="stretch")

        st.subheader("3. Theme & transition")
        names = list(THEMES) + ([deck.theme.name] if deck.theme.name not in THEMES else [])
        key = f"theme_{ss.rev}"
        st.selectbox("Theme", names, index=names.index(deck.theme.name), key=key, format_func=str.title,
                     on_change=_cb_deck_field, args=(key, "theme"))
        key = f"color_{ss.rev}"
        st.color_picker("Accent colour", _safe_color(deck.theme.primary_color, "#1F4E79"), key=key,
                        on_change=_cb_deck_field, args=(key, "color"))
        key = f"transition_{ss.rev}"
        st.selectbox("Transition", TRANSITIONS, index=TRANSITIONS.index(deck.transition), key=key,
                     format_func=str.title, on_change=_cb_deck_field, args=(key, "transition"))
        langs = list(LANG_LABEL) + ([deck.language] if deck.language not in LANG_LABEL else [])
        key = f"lang_{ss.rev}"
        st.selectbox("Deck language", langs, index=langs.index(deck.language), key=key,
                     format_func=lambda x: LANG_LABEL.get(x, x), on_change=_cb_deck_field, args=(key, "language"))
        key = f"dir_{ss.rev}"
        st.radio("Text direction", ["ltr", "rtl"], index=["ltr", "rtl"].index(deck.theme.direction), key=key,
                 horizontal=True, format_func={"ltr": "Left → right", "rtl": "Right → left"}.get,
                 on_change=_cb_deck_field, args=(key, "direction"))

        st.subheader("4. AI assistant (optional)")
        st.selectbox("Provider", PROVIDERS, key="ai_provider",
                     help="Everything works with AI off. Free options: Ollama (local), Groq, OpenRouter, "
                          "Hugging Face router, Gemini.")
        if ss.ai_provider == "OpenAI-compatible":
            st.selectbox("Service", list(PROVIDER_PRESETS), index=list(PROVIDER_PRESETS).index(ss.ai_preset),
                         key="w_ai_preset", on_change=_cb_preset)
            _persist_text("Base URL", "ai_base_url")
            _persist_text("Model", "ai_model")
            _persist_text("API key", "ai_key", type="password")
        elif ss.ai_provider == "Ollama (local)":
            _persist_text("Ollama URL", "ai_ollama_url")
            _persist_text("Model", "ai_ollama_model")
            st.caption("Ollama must run on the same machine as this app (it won't work on Streamlit Cloud).")
        elif ss.ai_provider == "Gemini":
            _persist_text("Model", "ai_gemini_model")
            _persist_text("API key", "ai_gemini_key", type="password")
        if ss.ai_provider != "Off":
            st.caption("🔒 Keys stay in this browser session only. They are never saved or exported.")

        st.subheader("5. Undo / Redo")
        c1, c2 = st.columns(2)
        c1.button("↶ Undo", on_click=_cb_undo, disabled=not ss.hist.can_undo, width="stretch")
        c2.button("↷ Redo", on_click=_cb_redo, disabled=not ss.hist.can_redo, width="stretch")

        st.subheader("6. Export / Save")
        if ss.export[0] != ss.rev:
            ss.export = (ss.rev, render_deck(deck).encode("utf-8"))
        st.download_button("⬇ Export presentation (.html)", data=ss.export[1], file_name=f"{_slug(deck.title)}.html",
                           mime="text/html", type="primary", on_click="ignore", width="stretch")
        st.caption("One file with everything inside. It opens in any browser, even offline.")
        st.download_button("💾 Save editable deck (.json)", data=deck.model_dump_json(indent=1).encode("utf-8"),
                           file_name=f"{_slug(deck.title)}.json", mime="application/json", on_click="ignore",
                           width="stretch")
        st.caption("Upload the .json later to continue editing.")


# ── slide editor ────────────────────────────────────────────────────────────

def _lines(text: str) -> list[str]:
    return [ln.strip() for ln in text.splitlines() if ln.strip()]


def _block_summary(b: Any) -> str:
    text = block_text(b) if b.type != "image" else (b.alt or b.caption or "image")
    text = re.sub(r"\s+", " ", text).strip()
    return text[:48] + ("…" if len(text) > 48 else "")


def default_block(kind: str, image_uri: str | None = None) -> Any:
    return {
        "text": lambda: TextBlock(text="New text"),
        "bullets": lambda: BulletsBlock(items=["First point", "Second point"]),
        "image": lambda: ImageBlock(src=image_uri or "", alt="Image"),
        "table": lambda: TableBlock(headers=["Column 1", "Column 2"], rows=[["", ""], ["", ""]]),
        "chart": lambda: ChartBlock(chart_type="bar", labels=["A", "B", "C"], series={"Values": [3, 5, 2]}),
        "code": lambda: CodeBlock(code="print('Hello, class!')"),
        "quote": lambda: QuoteBlock(text="Quote text", source="Author"),
        "quiz": lambda: QuizBlock(question="Your question?", options=["Option A", "Option B", "Option C"],
                                  answer_index=0),
    }[kind]()


def _edit_block_form(slide: Slide, b: Any, k: str) -> Any | None:
    """Render the form for one block; return the edited block when saved (None otherwise)."""
    with st.form(f"form_{k}_{b.id}", border=False):
        if b.type == "text":
            text = st.text_area("Text", b.text, height=110)
            new = lambda: TextBlock(text=text.strip())  # noqa: E731
        elif b.type == "bullets":
            items = st.text_area("One bullet per line", "\n".join(b.items), height=150)
            frag = st.checkbox("Reveal bullets one by one", b.fragments)
            new = lambda: BulletsBlock(items=_lines(items), fragments=frag)  # noqa: E731
        elif b.type == "image":
            st.image(b.src, width=220)
            alt = st.text_input("Alt text (read aloud by screen readers)", b.alt)
            caption = st.text_input("Caption", b.caption)
            replacement = st.file_uploader("Replace image", type=["png", "jpg", "jpeg", "gif", "webp"])

            def new() -> Any:
                src = b.src
                if replacement is not None:
                    src = image_to_data_uri(replacement.getvalue()) or b.src
                return ImageBlock(src=src, alt=alt, caption=caption)
        elif b.type == "table":
            import pandas as pd
            heads = st.text_input("Column headers (separate with |)", " | ".join(b.headers))
            cols = [f"c{j}" for j in range(len(b.headers))]
            frame = pd.DataFrame([r + [""] * (len(cols) - len(r)) for r in b.rows] or [[""] * len(cols)], columns=cols)
            config = {c: st.column_config.TextColumn(h or f"Column {j + 1}") for j, (c, h) in enumerate(zip(cols, b.headers))}
            edited = st.data_editor(frame, num_rows="dynamic", hide_index=True, column_config=config, width="stretch")

            def new() -> Any:
                headers = [h.strip() for h in heads.split("|")]
                rows = [[("" if pd.isna(v) else str(v)).strip() for v in r] for r in edited.values.tolist()]
                rows = [(r + [""] * len(headers))[:len(headers)] for r in rows if any(c for c in r)]
                return TableBlock(headers=headers, rows=rows)
        elif b.type == "chart":
            ctype = st.selectbox("Chart type", ["bar", "line", "pie"], ["bar", "line", "pie"].index(b.chart_type))
            labels = st.text_input("Labels (separate with |)", " | ".join(b.labels))
            series_text = st.text_area("Series: one per line, as  Name: 1 | 2 | 3",
                                       "\n".join(f"{n}: " + " | ".join(_fmt(v) for v in vals)
                                                 for n, vals in b.series.items()), height=100)

            def new() -> Any:
                series = {}
                for line in _lines(series_text):
                    name, _, values = line.rpartition(":") if ":" in line else ("Values", ":", line)
                    nums = [parse_number(v) for v in values.split("|")]
                    if any(v is None for v in nums):
                        raise OpError(f"'{line}' contains a value that is not a number")
                    series[name.strip() or "Values"] = nums
                return ChartBlock(chart_type=ctype, labels=[x.strip() for x in labels.split("|")],
                                  series=series, source_table_id=b.source_table_id)
        elif b.type == "code":
            lang = st.text_input("Language", b.language)
            code = st.text_area("Code", b.code, height=160)
            new = lambda: CodeBlock(language=lang.strip() or "text", code=code)  # noqa: E731
        elif b.type == "quote":
            text = st.text_area("Quote", b.text, height=90)
            source = st.text_input("Source", b.source)
            new = lambda: QuoteBlock(text=text.strip(), source=source.strip())  # noqa: E731
        else:  # quiz
            question = st.text_input("Question", b.question)
            options = st.text_area("Answer options, one per line", "\n".join(b.options), height=110)
            answer = st.number_input("Number of the correct option", 1, 20, b.answer_index + 1)
            new = lambda: QuizBlock(question=question.strip(), options=_lines(options),  # noqa: E731
                                    answer_index=int(answer) - 1)
        if st.form_submit_button("Save block", type="primary"):
            try:
                block = new()
            except (OpError, ValidationError) as exc:
                st.error(f"Not saved: {exc}")
                return None
            if block.type == "quiz" and not 0 <= block.answer_index < len(block.options):
                st.error("Not saved: the correct option number is larger than the number of options.")
                return None
            return block
    return None


def slide_editor(deck: Deck) -> None:
    ss = st.session_state
    slide = deck.slides[ss.cur]
    k = f"{ss.rev}_{slide.id}"
    st.markdown(f"#### ✏️ Slide {ss.cur + 1} of {len(deck.slides)}")
    if slide.source_ref:
        st.caption(f"From the source document: {slide.source_ref}")
    with st.form(f"slide_{k}"):
        title = st.text_input("Slide title", slide.title)
        layout = st.selectbox("Layout", LAYOUTS, LAYOUTS.index(slide.layout), format_func=LAYOUT_LABEL.get)
        notes = st.text_area("Speaker notes (press S in the presentation)", slide.notes, height=80)
        if st.form_submit_button("Save slide", type="primary"):
            ops = []
            if title != slide.title:
                ops.append(EditOp(op="update_title", slide_id=slide.id, payload={"title": title}))
            if layout != slide.layout:
                ops.append(EditOp(op="change_layout", slide_id=slide.id, payload={"layout": layout}))
            if notes != slide.notes:
                ops.append(EditOp(op="set_notes", slide_id=slide.id, payload={"notes": notes}))
            if ops and _run(ops, "Slide saved."):
                st.rerun()
    bullets, words = slide_density(slide)
    if bullets > MAX_BULLETS or words > MAX_WORDS:
        st.warning(f"This slide is crowded ({bullets} bullets, {words} words). Aim for at most "
                   f"{MAX_BULLETS} bullets and {MAX_WORDS} words: split it below or ask the AI.")
    st.markdown("**Content blocks**")
    if not slide.blocks:
        st.caption("This slide has no content yet. Add a block below.")
    for i, b in enumerate(slide.blocks):
        with st.expander(f"{i + 1}. {BLOCK_LABEL[b.type]}: {_block_summary(b)}", expanded=len(slide.blocks) == 1):
            edited = _edit_block_form(slide, b, k)
            if edited is not None:
                if _run([EditOp(op="rewrite_block", slide_id=slide.id, target_id=b.id,
                                payload={"block": edited.model_dump()})], "Block saved."):
                    st.rerun()
            c = st.columns(3)
            if c[0].button("🗑 Delete block", key=f"del_{k}_{b.id}"):
                if _run([EditOp(op="delete_block", slide_id=slide.id, target_id=b.id)], "Block deleted."):
                    st.rerun()
            if i > 0 and c[1].button("✂ New slide from here", key=f"split_{k}_{b.id}",
                                     help="Move this block and the ones below it to a new slide"):
                if _run([EditOp(op="split_slide", slide_id=slide.id, payload={"at_block_index": i})], "Slide split."):
                    st.rerun()
            if b.type == "table" and c[2].button("📊 Make a chart", key=f"chart_{k}_{b.id}"):
                if _run([EditOp(op="table_to_chart", slide_id=slide.id, target_id=b.id,
                                payload={"chart_type": "bar"})], "Chart created from the table."):
                    st.rerun()
    with st.expander("➕ Add a block"):
        kind = st.selectbox("Block type", BLOCK_TYPES, format_func=BLOCK_LABEL.get, key=f"addtype_{k}")
        image = None
        if kind == "image":
            image = st.file_uploader("Choose an image", type=["png", "jpg", "jpeg", "gif", "webp"], key=f"addimg_{k}")
        if st.button("Add block", key=f"addbtn_{k}", type="primary"):
            uri = image_to_data_uri(image.getvalue()) if image is not None else None
            if kind == "image" and not uri:
                st.error("Choose a PNG, JPEG, GIF or WebP image first.")
            elif kind == "quiz":
                q = default_block("quiz")
                if _run([EditOp(op="add_quiz", slide_id=slide.id, payload={
                        "question": q.question, "options": q.options, "answer_index": 0})], "Quiz added."):
                    st.rerun()
            elif _run([EditOp(op="add_block", slide_id=slide.id,
                              payload={"block": default_block(kind, uri).model_dump()})], "Block added."):
                st.rerun()
    if ss.cur < len(deck.slides) - 1 and st.button("⤓ Merge with the next slide", key=f"merge_{k}"):
        if _run([EditOp(op="merge_slides", slide_id=slide.id, target_id=deck.slides[ss.cur + 1].id)],
                "Slides merged."):
            st.rerun()


def preview(deck: Deck) -> None:
    ss = st.session_state
    st.markdown("#### 👁️ Live preview")
    whole = st.toggle("Play the whole deck", key="preview_whole")
    if whole:
        _iframe(render_deck(deck, start=ss.cur), height=380)
    else:
        _iframe(render_deck(deck, only=ss.cur, preview=True), height=340)
    st.caption("Click the preview, then use ← → (or Space) to move. S shows speaker notes, F goes full screen.")


# ── AI panel ────────────────────────────────────────────────────────────────

def _describe_op(op: EditOp, deck: Deck) -> str:
    names = {"update_title": "Change the title", "rewrite_block": "Rewrite a block", "add_block": "Add a block",
             "delete_block": "Remove a block", "split_slide": "Split into two slides", "change_layout": "Change layout",
             "set_notes": "Update speaker notes", "table_to_chart": "Turn the table into a chart",
             "add_quiz": "Add a quiz question"}
    label = names.get(op.op, op.op)
    if op.target_id:
        for s in deck.slides:
            for i, b in enumerate(s.blocks):
                if b.id == op.target_id:
                    label += f" (block {i + 1}: {BLOCK_LABEL[b.type]})"
    return f"**{label}**" + (f" — {op.rationale}" if op.rationale else "")


def _suggestion_view(deck: Deck, provider: Provider) -> None:
    ss = st.session_state
    sug_state = ss.suggestion
    suggestion = Suggestion.model_validate_json(sug_state["json"])
    try:
        before_i = _slide_index(deck, sug_state["slide_id"])
        after = apply_all(deck, suggestion.ops)
        after_i = _slide_index(after, sug_state["slide_id"])
    except OpError as exc:
        st.error(f"This suggestion no longer fits the deck ({exc}). Reject it and ask again.")
        if st.button("Reject", key="ai_reject_stale"):
            ss.suggestion = None
            st.rerun()
        return
    if sug_state["rev"] != ss.rev:
        st.info("You edited the deck after this suggestion was made; the preview below uses your latest version.")
    st.markdown(f"**Suggestion:** {suggestion.summary}  \n<small>Valid on attempt {sug_state['attempts']} of 3."
                "</small>", unsafe_allow_html=True)
    for op in suggestion.ops:
        st.markdown("- " + _describe_op(op, deck))
    c1, c2 = st.columns(2)
    with c1:
        st.caption("Before")
        _iframe(render_deck(deck, only=before_i, preview=True), height=300)
    with c2:
        extra = len(after.slides) - len(deck.slides)
        st.caption("After" + (f" (+{extra} new slide)" if extra > 0 else ""))
        _iframe(render_deck(after, only=after_i, preview=True), height=300)
    b1, b2, b3 = st.columns(3)
    if b1.button("✅ Accept", type="primary", width="stretch"):
        _commit(after, "Suggestion applied. Undo reverts it.")
        ss.suggestion = None
        st.rerun()
    if b2.button("✖ Reject", width="stretch"):
        ss.suggestion = None
        st.rerun()
    if b3.button("✎ Edit", width="stretch"):
        sug_state["editing"] = not sug_state.get("editing")
        st.rerun()
    if sug_state.get("editing"):
        text = st.text_area("Edit the suggested changes (JSON)", suggestion.model_dump_json(indent=2), height=260,
                            key=f"ai_edit_{sug_state['json'].__hash__()}")
        if st.button("Check and preview my edits"):
            try:
                edited, _ = validate_suggestion(text, deck, sug_state["slide_id"])
                sug_state.update(json=edited.model_dump_json(), editing=False, rev=ss.rev)
                st.rerun()
            except ValueError as exc:
                st.error(f"Your edit is not valid yet: {exc}")


def _measure_ai(deck: Deck, provider: Provider) -> None:
    slides = deck.slides[:10]
    stats: Counter = Counter()
    problems: list[str] = []
    bar = st.progress(0.0, text="Measuring…")
    for i, s in enumerate(slides, 1):
        try:
            _, _, attempt = request_suggestion(provider, deck, s.id)
            stats[f"attempt {attempt}"] += 1
        except AIError as exc:
            kind = "invalid" if "invalid answer" in str(exc) else "error"
            stats[kind] += 1
            problems.append(f"Slide {deck.slides.index(s) + 1}: {exc}")
        bar.progress(i / len(slides), text=f"Measured {i} of {len(slides)} slides")
    total = len(slides)
    valid = stats["attempt 1"] + stats["attempt 2"]
    st.metric("Valid on 1st or 2nd attempt", f"{valid / total:.0%}", help="Target: at least 90%")
    st.write({"1st attempt": stats["attempt 1"], "2nd attempt": stats["attempt 2"],
              "3rd attempt": stats["attempt 3"], "invalid 3x": stats["invalid"], "network/provider errors": stats["error"]})
    for p in problems:
        st.caption(p)


def ai_panel(deck: Deck) -> None:
    ss = st.session_state
    st.markdown("#### ✨ AI suggestions")
    provider = make_provider()
    if provider is None:
        st.info("AI is off, and every feature works without it. To get suggestions, choose a free provider "
                "in the sidebar (section 4).")
        return
    slide = deck.slides[ss.cur]
    instruction = st.text_input("What should the AI improve? (optional)", key="ai_instruction",
                                placeholder="e.g. Turn this paragraph into 4 short bullets for 12-year-olds")
    if st.button(f"Suggest improvements for slide {ss.cur + 1}", type="primary"):
        with st.spinner("Asking the AI (up to 30 s)…"):
            try:
                suggestion, _, attempts = request_suggestion(provider, deck, slide.id, instruction)
                ss.suggestion = {"rev": ss.rev, "slide_id": slide.id, "json": suggestion.model_dump_json(),
                                 "attempts": attempts, "editing": False}
            except AIError as exc:
                st.error(str(exc))
    if ss.suggestion:
        _suggestion_view(deck, provider)
    with st.expander("📏 Measure AI validity on this deck (up to 10 slides)"):
        st.caption("Sends one request per slide and reports how often the AI's answer validates on the first "
                   "or second attempt. Nothing is changed in your deck.")
        if st.button("Run measurement"):
            _measure_ai(deck, provider)


# ── page ────────────────────────────────────────────────────────────────────

def welcome() -> None:
    st.title("DocToDeck")
    st.markdown("#### Turn a document into a clean, interactive presentation in minutes.")
    c = st.columns(3)
    c[0].markdown("**1 · Upload**  \nA Word (.docx), PDF, web page (.html) or PowerPoint (.pptx) file, "
                  "in the sidebar.")
    c[1].markdown("**2 · Edit**  \nFix titles, bullets, tables and images, add quizzes and charts, and check "
                  "the live preview.")
    c[2].markdown("**3 · Export**  \nDownload one .html file. It plays in any browser, even without internet.")
    st.info("No file handy? Click **English sample** or **Arabic sample** in the sidebar.")


def main() -> None:
    st.set_page_config(page_title="DocToDeck", page_icon="🎞️", layout="wide")
    ss = _ss()
    sidebar()
    for kind, message in ss.flash:
        st.toast(message, icon="✅") if kind == "success" else st.error(message)
    ss.flash = []
    deck = _deck()
    if deck is None:
        welcome()
        return
    key = f"decktitle_{ss.rev}"
    st.text_input("Presentation title", deck.title, key=key, on_change=_cb_deck_field, args=(key, "title"))
    info = ss.parse_info or {}
    facts = [f"{len(deck.slides)} slides", f"{density_ratio(deck):.0%} of slides within the 6-bullet / 60-word limits"]
    if info.get("name"):
        facts.append(f"from {info['name']} in {info.get('seconds', 0):.1f} s")
    if info.get("coverage") is not None:
        facts.append(f"{info['coverage']:.0%} of the source text kept")
    st.caption(" · ".join(facts))
    for w in ss.warnings:
        st.warning(w)
    left, right = st.columns([1, 1.25], gap="large")
    with left:
        slide_editor(deck)
    with right:
        preview(deck)
    st.divider()
    ai_panel(deck)


def _stable_module() -> Any:
    """Streamlit re-executes this file on every interaction, which would redefine the pydantic
    classes and make decks kept in session_state fail validation. So the script imports this
    same file once as a normal module (re-imported only when the file changes) and runs its UI."""
    import importlib.util
    import os
    import sys
    path = os.path.abspath(__file__)
    mtime = os.path.getmtime(path)
    module = sys.modules.get("doctodeck_app")
    if module is None or getattr(module, "_SOURCE_MTIME", None) != mtime:
        spec = importlib.util.spec_from_file_location("doctodeck_app", path)
        module = importlib.util.module_from_spec(spec)
        sys.modules["doctodeck_app"] = module
        spec.loader.exec_module(module)
        module._SOURCE_MTIME = mtime
    return module


if __name__ == "__main__":
    _stable_module().main()
