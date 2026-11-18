import os, io, re, sys, math, zlib, base64, functools, hmac, hashlib, time, sqlite3, html, asyncio
from urllib.parse import quote
from PIL import Image, ImageDraw, ImageFilter, ImageFont
import discord
from discord import app_commands
from discord.ext import commands
from aiohttp import web

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

TOKEN = os.environ.get("DISCORD_TOKEN", "")
GUILD_ID = int(os.environ.get("GUILD_ID", "0") or 0)
DASH_PASS = os.environ.get("DASH_PASSWORD", "change-me")
PORT = int(os.environ.get("PORT", "8080"))
DATA_DIR = os.environ.get("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)
COLOR = 0x967A62
DEFAULT_PHOTOS_CH = 1501306907577815132  # روم الصور الرئيسي (يُعدَّل من الداشبورد)

# ───────────── الصور والأيقونات والإيموجي ─────────────
W, H = 1170, 1130
BG = (150, 122, 96)
CENTERS = [(585, 389), (475, 513), (695, 513), (363, 638), (585, 638), (805, 638)]
R = 108
ASSETS = os.path.join(DATA_DIR, "assets")
FONT_PATH = os.path.join(ASSETS, "font.ttf")        # خط مخصص (اختياري عبر /set_font)
DEFAULT_FONT = os.path.join(ASSETS, "default.ttf")  # الخط المدمج داخل الملف
_FC = {}

# ── محرك الحروف العربية (تشكيل + ترتيب) بدون مكتبات خارجية ──
_FORMS = [
    (0x621, 0xFE80, 0, 0, 0), (0x622, 0xFE81, 0xFE82, 0, 0), (0x623, 0xFE83, 0xFE84, 0, 0),
    (0x624, 0xFE85, 0xFE86, 0, 0), (0x625, 0xFE87, 0xFE88, 0, 0), (0x626, 0xFE89, 0xFE8A, 0xFE8B, 0xFE8C),
    (0x627, 0xFE8D, 0xFE8E, 0, 0), (0x628, 0xFE8F, 0xFE90, 0xFE91, 0xFE92), (0x629, 0xFE93, 0xFE94, 0, 0),
    (0x62A, 0xFE95, 0xFE96, 0xFE97, 0xFE98), (0x62B, 0xFE99, 0xFE9A, 0xFE9B, 0xFE9C),
    (0x62C, 0xFE9D, 0xFE9E, 0xFE9F, 0xFEA0), (0x62D, 0xFEA1, 0xFEA2, 0xFEA3, 0xFEA4),
    (0x62E, 0xFEA5, 0xFEA6, 0xFEA7, 0xFEA8), (0x62F, 0xFEA9, 0xFEAA, 0, 0), (0x630, 0xFEAB, 0xFEAC, 0, 0),
    (0x631, 0xFEAD, 0xFEAE, 0, 0), (0x632, 0xFEAF, 0xFEB0, 0, 0),
    (0x633, 0xFEB1, 0xFEB2, 0xFEB3, 0xFEB4), (0x634, 0xFEB5, 0xFEB6, 0xFEB7, 0xFEB8),
    (0x635, 0xFEB9, 0xFEBA, 0xFEBB, 0xFEBC), (0x636, 0xFEBD, 0xFEBE, 0xFEBF, 0xFEC0),
    (0x637, 0xFEC1, 0xFEC2, 0xFEC3, 0xFEC4), (0x638, 0xFEC5, 0xFEC6, 0xFEC7, 0xFEC8),
    (0x639, 0xFEC9, 0xFECA, 0xFECB, 0xFECC), (0x63A, 0xFECD, 0xFECE, 0xFECF, 0xFED0),
    (0x641, 0xFED1, 0xFED2, 0xFED3, 0xFED4), (0x642, 0xFED5, 0xFED6, 0xFED7, 0xFED8),
    (0x643, 0xFED9, 0xFEDA, 0xFEDB, 0xFEDC), (0x644, 0xFEDD, 0xFEDE, 0xFEDF, 0xFEE0),
    (0x645, 0xFEE1, 0xFEE2, 0xFEE3, 0xFEE4), (0x646, 0xFEE5, 0xFEE6, 0xFEE7, 0xFEE8),
    (0x647, 0xFEE9, 0xFEEA, 0xFEEB, 0xFEEC), (0x648, 0xFEED, 0xFEEE, 0, 0), (0x649, 0xFEEF, 0xFEF0, 0, 0),
    (0x64A, 0xFEF1, 0xFEF2, 0xFEF3, 0xFEF4), (0x640, 0x640, 0x640, 0x640, 0x640),
]
_J = {chr(c): tuple(chr(x) if x else None for x in v) for c, *v in _FORMS}
_LA = {"ا": (0xFEFB, 0xFEFC), "أ": (0xFEF7, 0xFEF8), "إ": (0xFEF9, 0xFEFA), "آ": (0xFEF5, 0xFEF6)}
_HAS_AR = re.compile("[\u0600-\u06FF]")
_LTR = re.compile(r"[A-Za-z0-9\u0660-\u0669](?:[A-Za-z0-9\u0660-\u0669 .,:_\-@#/'+&]*[A-Za-z0-9\u0660-\u0669])?")
_MIRROR = str.maketrans("()[]{}<>", ")(][}{><")


def _shape(s):
    s = re.sub("[\u064B-\u065F\u0670]", "", s)
    items, i = [], 0
    while i < len(s):
        c = s[i]
        if c == "ل" and i + 1 < len(s) and s[i + 1] in _LA:
            iso, fin = _LA[s[i + 1]]
            items.append((c, (chr(iso), chr(fin), None, None)))
            i += 2
            continue
        items.append((c, _J.get(c)))
        i += 1
    out = []
    for k, (c, f) in enumerate(items):
        if not f:
            out.append(c)
            continue
        prev = items[k - 1][1] if k else None
        nxt = items[k + 1][1] if k + 1 < len(items) else None
        jp = bool(prev and prev[2] and f[1])
        jn = bool(f[2] and nxt and nxt[1])
        out.append((f[3] if jp and jn else f[1] if jp else f[2] if jn else f[0]) or f[0])
    return "".join(out)


def _vis(s):
    """نص منطقي → نص مرئي (يُرسم من اليسار لليمين) مع الحفاظ على الأرقام واللاتيني"""
    if not _HAS_AR.search(s):
        return s
    s = _shape(s)
    parts, pos = [], 0
    for m in _LTR.finditer(s):
        if m.start() > pos:
            parts.append((s[pos:m.start()], True))
        parts.append((m.group(), False))
        pos = m.end()
    if pos < len(s):
        parts.append((s[pos:], True))
    return "".join(t[::-1].translate(_MIRROR) if rtl else t for t, rtl in reversed(parts))


_FONT_READY = False


def _font(size):
    global _FONT_READY
    if size not in _FC:
        path = FONT_PATH if os.path.exists(FONT_PATH) else DEFAULT_FONT
        if path == DEFAULT_FONT and not os.path.exists(DEFAULT_FONT):
            os.makedirs(ASSETS, exist_ok=True)
            with open(DEFAULT_FONT, "wb") as fh:
                fh.write(zlib.decompress(base64.b64decode("".join(_FONT_B64))))
        try:
            _FC[size] = ImageFont.truetype(path, size, layout_engine=ImageFont.Layout.BASIC)
        except Exception:
            _FC[size] = ImageFont.load_default(size=size)
    return _FC[size]


def _fit(text, size, maxw, minsize=22):
    while size > minsize and _font(size).getlength(_vis(text)) > maxw:
        size -= 2
    return _font(size)


def _put(d, xy, text, font, fill, anchor="ra"):
    d.text(xy, _vis(text), font=font, fill=fill, anchor=anchor)


# ── الأشكال الأساسية ──
def _png(im):
    b = io.BytesIO()
    im.save(b, "PNG")
    return b.getvalue()


def _bg(w, h, c1=(150, 122, 96), c2=(104, 82, 63)):
    g = Image.linear_gradient("L").resize((w, h))
    return Image.composite(Image.new("RGB", (w, h), c2), Image.new("RGB", (w, h), c1), g)


@functools.lru_cache(maxsize=16)
def _mark(height):
    S = 2
    full = Image.new("RGBA", (W * S, H * S), (0, 0, 0, 0))
    sh = Image.new("L", full.size, 0)
    d = ImageDraw.Draw(sh)
    for cx, cy in CENTERS:
        o = 16
        d.polygon([(cx * S, (cy - R + o) * S), ((cx + R) * S, (cy + o) * S),
                   (cx * S, (cy + R + o) * S), ((cx - R) * S, (cy + o) * S)], fill=160)
    sh = sh.filter(ImageFilter.GaussianBlur(18 * S))
    shadow = Image.new("RGBA", full.size, (70, 52, 36, 255))
    shadow.putalpha(sh)
    full = Image.alpha_composite(full, shadow)
    for i, (cx, cy) in enumerate(CENTERS):
        top, bot = ((205, 190, 180), (190, 175, 166)) if i == 0 else ((243, 235, 230), (252, 246, 242))
        n = 2 * R * S
        tile = Image.composite(Image.new("RGB", (n, n), bot), Image.new("RGB", (n, n), top),
                               Image.linear_gradient("L").resize((n, n)))
        m = Image.new("L", (n, n), 0)
        ImageDraw.Draw(m).polygon([(n // 2, 0), (n, n // 2), (n // 2, n), (0, n // 2)], fill=255)
        full.paste(tile, ((cx - R) * S, (cy - R) * S), m)
    full = full.crop((200 * S, 230 * S, 950 * S, 830 * S))
    r = height / full.height
    return full.resize((max(1, int(full.width * r)), height), Image.LANCZOS)


def _faded(im, a):
    im = im.copy()
    im.putalpha(im.getchannel("A").point(lambda v: int(v * a)))
    return im


def logo(size=1024):
    im = Image.new("RGB", (size, size), BG)
    mk = _mark(int(size * .58))
    im.paste(mk, ((size - mk.width) // 2, (size - mk.height) // 2), mk)
    return _png(im)


def avatar(size=512):
    return logo(size)


# ── الأيقونات (إيموجي البوت) بنفس تصميم اللوقو ──
_BROWN, _GREEN, _RED, _AMBER = (104, 78, 56), (40, 140, 88), (188, 62, 54), (214, 140, 24)
_COL = {"check": _GREEN, "cross": _RED, "ban": _RED, "warn": _AMBER, "stop": _RED, "star": _AMBER,
        "crown": _AMBER, "event": _AMBER}


class _G:
    def __init__(self, d, k, col):
        self.d, self.k, self.c = d, k, col

    def t(self, x, y):
        return (50 + (x - 50) * .9) * self.k, (50 + (y - 50) * .9) * self.k

    def line(self, pts, w=8):
        p = [self.t(*q) for q in pts]
        wd, r = int(w * .9 * self.k), w * .9 * self.k / 2
        self.d.line(p, fill=self.c, width=wd, joint="curve")
        for x, y in (p[0], p[-1]):
            self.d.ellipse((x - r, y - r, x + r, y + r), fill=self.c)

    def poly(self, pts):
        self.d.polygon([self.t(*q) for q in pts], fill=self.c)

    def circ(self, cx, cy, r, w=0):
        (x, y), rr = self.t(cx, cy), r * .9 * self.k
        if w:
            self.d.ellipse((x - rr, y - rr, x + rr, y + rr), outline=self.c, width=int(w * .9 * self.k))
        else:
            self.d.ellipse((x - rr, y - rr, x + rr, y + rr), fill=self.c)

    def rect(self, x0, y0, x1, y1, w=0, rad=4):
        a, b = self.t(x0, y0), self.t(x1, y1)
        self.d.rounded_rectangle((a[0], a[1], b[0], b[1]), radius=rad * self.k,
                                 outline=self.c if w else None, fill=None if w else self.c,
                                 width=int(w * .9 * self.k) if w else 0)

    def arc(self, cx, cy, r, a0, a1, w=8):
        (x, y), rr = self.t(cx, cy), r * .9 * self.k
        self.d.arc((x - rr, y - rr, x + rr, y + rr), a0, a1, fill=self.c, width=int(w * .9 * self.k))


def _star(g, cx, cy, ro, ri, n):
    g.poly([(cx + (ro if i % 2 == 0 else ri) * math.cos(math.radians(-90 + 180 / n * i)),
             cy + (ro if i % 2 == 0 else ri) * math.sin(math.radians(-90 + 180 / n * i))) for i in range(2 * n)])


def _gl_undo(g):
    g.arc(50, 50, 20, 40, 330, 8)
    a = math.radians(330)
    px, py, tx, ty = 50 + 20 * math.cos(a), 50 + 20 * math.sin(a), -math.sin(a), math.cos(a)
    g.poly([(px + tx * 12, py + ty * 12), (px - tx * 3 - ty * 10, py - ty * 3 + tx * 10),
            (px - tx * 3 + ty * 10, py - ty * 3 - tx * 10)])


def _gl_users(g):
    g.circ(50, 36, 9)
    g.poly([(50 + 21 * math.cos(math.radians(a)), 68 - 19 * math.sin(math.radians(a))) for a in range(0, 181, 12)])


def _gl_gear(g):
    g.circ(50, 50, 15, w=8)
    for i in range(8):
        a = math.radians(i * 45)
        g.line([(50 + 19 * math.cos(a), 50 + 19 * math.sin(a)), (50 + 27 * math.cos(a), 50 + 27 * math.sin(a))], 9)


def _gl_forum(g):
    for cx, cy in [(50, 32), (42, 46), (58, 46), (34, 60), (50, 60), (66, 60)]:
        g.poly([(cx, cy - 8), (cx + 8, cy), (cx, cy + 8), (cx - 8, cy)])


_GLYPHS = {
    "check": lambda g: g.line([(30, 52), (44, 65), (70, 36)], 10),
    "cross": lambda g: (g.line([(33, 33), (67, 67)], 10), g.line([(67, 33), (33, 67)], 10)),
    "plus": lambda g: (g.line([(50, 29), (50, 71)], 10), g.line([(29, 50), (71, 50)], 10)),
    "exit": lambda g: (g.line([(52, 32), (34, 32), (34, 68), (52, 68)], 8), g.line([(44, 50), (70, 50)], 8),
                       g.line([(60, 40), (70, 50), (60, 60)], 8)),
    "ban": lambda g: (g.circ(50, 50, 21, w=8), g.line([(37, 63), (63, 37)], 8)),
    "undo": _gl_undo,
    "warn": lambda g: (g.line([(50, 32), (69, 65), (31, 65), (50, 32)], 7), g.line([(50, 45), (50, 55)], 7),
                       g.circ(50, 60.5, 3.6)),
    "star": lambda g: _star(g, 50, 52, 26, 11, 5),
    "pen": lambda g: (g.line([(42, 58), (65, 35)], 12), g.poly([(30, 70), (35, 55), (45, 65)])),
    "log": lambda g: (g.rect(34, 28, 66, 72, w=6, rad=5), g.line([(41, 41), (59, 41)], 5),
                      g.line([(41, 51), (59, 51)], 5), g.line([(41, 61), (52, 61)], 5)),
    "event": lambda g: _star(g, 50, 50, 28, 14, 8),
    "crown": lambda g: (g.poly([(29, 62), (29, 38), (40, 50), (50, 32), (60, 50), (71, 38), (71, 62)]),
                        g.rect(29, 64, 71, 70, rad=2)),
    "megaphone": lambda g: (g.poly([(30, 43), (46, 43), (70, 29), (70, 71), (46, 57), (30, 57)]),
                            g.line([(40, 58), (44, 72)], 7)),
    "clock": lambda g: (g.circ(50, 50, 23, w=7), g.line([(50, 50), (50, 35)], 6), g.line([(50, 50), (61, 57)], 6)),
    "users": _gl_users,
    "mail": lambda g: (g.rect(29, 36, 71, 64, w=6, rad=4), g.line([(31, 38), (50, 53), (69, 38)], 6)),
    "photo": lambda g: (g.rect(28, 34, 72, 66, w=6, rad=4), g.circ(41, 45, 4.5),
                        g.line([(32, 62), (46, 50), (55, 59), (61, 53), (69, 62)], 5)),
    "stop": lambda g: g.rect(34, 34, 66, 66, rad=6),
    "inbox": lambda g: (g.line([(28, 52), (36, 34), (64, 34), (72, 52)], 6), g.rect(28, 52, 72, 68, w=6, rad=3),
                        g.line([(28, 52), (42, 52), (46, 58), (54, 58), (58, 52), (72, 52)], 6)),
    "gear": _gl_gear,
    "chart": lambda g: (g.rect(31, 50, 41, 70, rad=2), g.rect(45, 38, 55, 70, rad=2), g.rect(59, 28, 69, 70, rad=2)),
    "forum": _gl_forum,
}
ICONS = list(_GLYPHS)


@functools.lru_cache(maxsize=64)
def _icon_big(name, px=512):
    k = px / 100
    dia = lambda dy: [(50 * k, (10 + dy) * k), (90 * k, (50 + dy) * k), (50 * k, (90 + dy) * k), (10 * k, (50 + dy) * k)]
    sh = Image.new("L", (px, px), 0)
    ImageDraw.Draw(sh).polygon(dia(5), fill=150)
    sh = sh.filter(ImageFilter.GaussianBlur(3 * k))
    base = Image.new("RGBA", (px, px), (60, 44, 30, 255))
    base.putalpha(sh)
    tile = Image.composite(Image.new("RGB", (px, px), (252, 247, 243)), Image.new("RGB", (px, px), (233, 222, 213)),
                           Image.linear_gradient("L").resize((px, px)))
    m = Image.new("L", (px, px), 0)
    ImageDraw.Draw(m).polygon(dia(0), fill=255)
    base.paste(tile, (0, 0), m)
    gl = Image.new("RGBA", (px, px), (0, 0, 0, 0))
    _GLYPHS[name](_G(ImageDraw.Draw(gl), k, _COL.get(name, _BROWN)))
    return Image.alpha_composite(base, gl)


@functools.lru_cache(maxsize=64)
def icon_png(name, size=128):
    return _png(_icon_big(name).resize((size, size), Image.LANCZOS))


# ── بطاقات الإمبيد ──
KIND = {"apply": ("forum", (214, 190, 168)), "request": ("inbox", (214, 190, 168)), "panel": ("crown", (230, 185, 90)),
        "gpanel": ("megaphone", (214, 190, 168)), "gnew": ("megaphone", (79, 183, 131)), "gend": ("stop", (229, 100, 93)),
        "photos": ("photo", (214, 190, 168)), "event": ("event", (230, 185, 90)), "warn": ("warn", (230, 172, 79)),
        "invite": ("mail", (214, 190, 168)), "kick": ("exit", (229, 100, 93)), "ban": ("ban", (229, 100, 93)),
        "ok": ("check", (79, 183, 131)), "no": ("cross", (229, 100, 93))}


def card(kind, title, sub="", extra="", w=1100, h=340):
    icon, accent = KIND[kind]
    im = _bg(w, h, (148, 120, 94), (98, 77, 58))
    mk = _faded(_mark(int(h * 1.35)), .15)
    im.paste(mk, (-int(h * .15), (h - mk.height) // 2), mk)
    ic = _icon_big(icon).resize((250, 250), Image.LANCZOS)
    ix = w - 44 - 250
    im.paste(ic, (ix, (h - 250) // 2 - 4), ic)
    d = ImageDraw.Draw(im)
    xr, maxw = ix - 34, ix - 34 - 44
    rows = [(title, _fit(title, 88, maxw), (253, 248, 244))]
    if sub:
        rows.append((sub, _fit(sub, 46, maxw, 24), (240, 228, 218)))
    if extra:
        rows.append((extra, _fit(extra, 34, maxw, 20), (216, 198, 184)))
    hs = [int(f.size * 1.3) for _, f, _ in rows]
    y = (h - 10 - sum(hs) - 8 * (len(rows) - 1)) // 2
    for (t, f, col), hh in zip(rows, hs):
        _put(d, (xr + 2, y + 3), t, f, (58, 42, 30))
        _put(d, (xr, y), t, f, col)
        y += hh + 8
    d.rectangle((0, h - 10, w, h), fill=accent)
    return _png(im)


def banner(title, sub, tags, w=1600, h=500):
    im = _bg(w, h, (166, 137, 108), (118, 94, 72))
    mk = _mark(int(h * .74))
    im.paste(mk, (int(w * .07), (h - mk.height) // 2), mk)
    d = ImageDraw.Draw(im)
    xr, maxw = w - int(w * .07), w - int(w * .07) * 2 - mk.width - 60
    _put(d, (xr, int(h * .17)), title, _fit(title, 150, maxw), (253, 248, 244))
    _put(d, (xr, int(h * .55)), sub, _fit(sub, 50, maxw), (240, 228, 218))
    if tags:
        _put(d, (xr, int(h * .71)), tags, _fit(tags, 36, maxw), (216, 198, 184))
    return _png(im)


def social(title, sub, w=1280, h=640):
    im = _bg(w, h, (166, 137, 108), (118, 94, 72))
    mk = _mark(int(h * .50))
    im.paste(mk, ((w - mk.width) // 2, int(h * .07)), mk)
    d = ImageDraw.Draw(im)
    _put(d, (w // 2, int(h * .72)), title, _fit(title, 100, w - 120), (253, 248, 244), "ma")
    _put(d, (w // 2, int(h * .88)), sub, _fit(sub, 40, w - 120), (240, 228, 218), "ma")
    return _png(im)


def icon_sheet():
    cols, cell = 6, 150
    rows = -(-len(ICONS) // cols)
    im = _bg(cols * cell + 20, rows * cell + 20, (166, 137, 108), (118, 94, 72))
    for i, n in enumerate(ICONS):
        ic = _icon_big(n).resize((128, 128), Image.LANCZOS)
        im.paste(ic, (20 + (i % cols) * cell - 10, 20 + (i // cols) * cell - 10), ic)
    return _png(im)


async def acard(kind, title, sub="", extra=""):
    data = await asyncio.to_thread(card, kind, title, sub, extra)
    return discord.File(io.BytesIO(data), filename=f"{kind}.png")


async def send_card(dest, kind, title, sub="", extra="", text=None, color=COLOR, view=None, content=None,
                    fields=None, **kw):
    e = discord.Embed(description=text, color=color)
    for n, v, inl in fields or []:
        e.add_field(name=n, value=v, inline=inl)
    e.set_image(url=f"attachment://{kind}.png")
    args = dict(embed=e, file=await acard(kind, title, sub, extra), **kw)
    if content:
        args["content"] = content
    if view is not None:
        args["view"] = view
    return await dest.send(**args)


# ── إيموجي البوت (Application Emojis) ──
EMO = {}


def em(n):
    return str(EMO[n]) if n in EMO else ""


def emo(n):
    return EMO.get(n)


async def load_emojis(force=False):
    try:
        have = {e.name: e for e in await bot.fetch_application_emojis()}
    except Exception as ex:
        print("[تنبيه] تعذر جلب إيموجي التطبيق (تحتاج discord.py 2.5+):", ex)
        return
    for n in ICONS:
        key, e = "fb_" + n, have.get("fb_" + n)
        try:
            if e and force:
                await e.delete()
                e = None
            if not e:
                e = await bot.create_application_emoji(name=key, image=await asyncio.to_thread(icon_png, n))
        except Exception as ex:
            print(f"[تنبيه] فشل رفع الإيموجي {key}:", ex)
            continue
        EMO[n] = e
    print(f"[OK] إيموجي البوت جاهزة: {len(EMO)}/{len(ICONS)}")


def make_assets():
    name = os.environ.get("BOT_NAME", "بوت المنتديات")
    for sub in ("images/icons", "images/cards"):
        os.makedirs(sub, exist_ok=True)
    files = {"logo.png": logo(), "avatar.png": avatar(),
             "banner.png": banner(name, "إدارة المنتديات والتجمعات في ديسكورد", "طلبات  •  رتب ورومات  •  تجمعات  •  لوحة تحكم"),
             "social-preview.png": social(name, "إدارة المنتديات والتجمعات في ديسكورد"), "icons.png": icon_sheet()}
    for n in ICONS:
        files[f"icons/{n}.png"] = icon_png(n)
    samples = {"apply": ("تقديم منتدى", "قدّم طلب إنشاء منتداك", ""), "request": ("طلب منتدى جديد", "صقور الشمال", "العدد: 12  •  تيك توك: @falcons"),
               "panel": ("لوحة تحكم المنتدى", "صقور الشمال", ""), "gpanel": ("لوحة التجمعات", "أعلن تجمعك أو أنهه", ""),
               "gnew": ("تجمع جديد", "Dream City", "الرمز: DC"), "gend": ("انتهى التجمع", "Dream City", "الرمز: DC"),
               "event": ("فعالية جديدة", "ليلة المسابقات", "الجائزة: 100 ألف"), "warn": ("تحذير", "صقور الشمال", "2/3"),
               "invite": ("دعوة دخول", "صقور الشمال", ""), "kick": ("إخراج من المنتدى", "صقور الشمال", "")}
    for k, (t, s, x) in samples.items():
        files[f"cards/{k}.png"] = card(k, t, s, x)
    for n, data in files.items():
        with open(os.path.join("images", n), "wb") as fh:
            fh.write(data)
        print("OK images/" + n)


# ───────────── قاعدة البيانات ─────────────
con = sqlite3.connect(os.path.join(DATA_DIR, "data.db"), check_same_thread=False)
con.row_factory = sqlite3.Row
con.executescript("""
CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS forums(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, owner_id INTEGER,
  tiktok TEXT, size TEXT, status TEXT, role_id INTEGER, category_id INTEGER, panel_id INTEGER, chat_id INTEGER);
CREATE TABLE IF NOT EXISTS members(forum_id INTEGER, user_id INTEGER, banned INTEGER DEFAULT 0, deputy INTEGER DEFAULT 0, PRIMARY KEY(forum_id,user_id));
CREATE TABLE IF NOT EXISTS cooldowns(user_id INTEGER PRIMARY KEY, until INTEGER, from_forum INTEGER);
CREATE TABLE IF NOT EXISTS warnings(id INTEGER PRIMARY KEY AUTOINCREMENT, forum_id INTEGER, user_id INTEGER, reason TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS logs(id INTEGER PRIMARY KEY AUTOINCREMENT, forum_id INTEGER, ts INTEGER, text TEXT);
CREATE TABLE IF NOT EXISTS gatherings(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, server TEXT,
  symbol TEXT, channel_id INTEGER, message_id INTEGER, active INTEGER DEFAULT 1);
""")
for _sql in ("ALTER TABLE members ADD COLUMN deputy INTEGER DEFAULT 0",
             "ALTER TABLE gatherings ADD COLUMN forum_id INTEGER",
             "ALTER TABLE forums ADD COLUMN gather_id INTEGER",
             "ALTER TABLE forums ADD COLUMN photos_id INTEGER",
             "ALTER TABLE gatherings ADD COLUMN pub INTEGER DEFAULT 0"):
    try:
        con.execute(_sql)
        con.commit()
    except sqlite3.OperationalError:
        pass


def q(sql, a=()):
    cur = con.execute(sql, a)
    con.commit()
    return cur


def one(sql, a=()):
    return con.execute(sql, a).fetchone()


def allrows(sql, a=()):
    return con.execute(sql, a).fetchall()


SETTING_KEYS = {
    "requests_ch": "روم طلبات المنتديات (ID)",
    "notices_ch": "روم إشعارات التجمعات (ID)",
    "photos_ch": "روم الصور الرئيسي (ID)",
    "gather_ping_role": "رتبة التجمع - تنمنشن (ID)",
    "gather_manager_role": "رتبة مسؤول التجمعات (ID)",
    "admin_role": "رتبة الإدارة (ID)",
    "min_members": "الحد الأدنى لأعضاء المنتدى (رقم، الافتراضي 5)",
    "max_forums": "أقصى عدد منتديات للشخص الواحد (الافتراضي 1)",
    "cooldown_days": "أيام الانتظار بعد الخروج من منتدى (الافتراضي 3، و0 = بدون)",
    "max_deputies": "أقصى عدد نواب للمنتدى (الافتراضي 2)",
    "max_warns": "عدد التحذيرات اللي يطلّع العضو تلقائياً (الافتراضي 3، و0 = بدون)",
    "voice_count": "عدد الرومات الصوتية للمنتدى (الافتراضي 4)",
    "chat_count": "عدد رومات الشات للمنتدى (الافتراضي 2)",
    "voice_name": "اسم الرومات الصوتية (فاضي = اسم المنتدى)",
    "chat_name": "اسم رومات الشات (الافتراضي شات)",
    "owner_name": "اسم روم الأونر (الافتراضي اونر)",
    "pub_gather_ch": "روم لوحة التجمع العام (ID)",
    "pub_mention": "منشن التجمع العام (1 = مفعّل، 0 = بدون)",
    "pub_role": "رتبة منشن التجمع العام (ID)",
    "pub_everyone": "من ينشئ التجمع العام (1 = الكل، 0 = مسؤولو التجمعات)",
}


def get(k):
    r = one("SELECT v FROM settings WHERE k=?", (k,))
    return r["v"] if r and r["v"] else None


def put(k, v):
    q("INSERT INTO settings(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, str(v)))


def num(k, default):
    v = get(k)
    try:
        return int(v) if v is not None else default
    except ValueError:
        return default


def add_log(fid, text):
    q("INSERT INTO logs(forum_id,ts,text) VALUES(?,?,?)", (fid, int(time.time()), text))


def has_role(m, key):
    rid = get(key)
    return bool(rid) and any(str(r.id) == rid for r in m.roles)


def is_admin(m):
    return m.guild_permissions.administrator or has_role(m, "admin_role")


P = discord.PermissionOverwrite

# ───────────── إنشاء المنتدى ─────────────
PANEL_BUTTONS = [("invite", "دعوة", "plus"), ("kick", "إخراج", "exit"), ("ban", "باند", "ban"),
                 ("unban", "فك باند", "undo"), ("warn", "تحذير", "warn"), ("event", "فعالية", "event"),
                 ("log", "اللوق", "log"), ("deputy", "نائب", "star"), ("rename", "الاسم", "pen")]
OWNER_ONLY = {"rename", "deputy"}


_AR_DIGITS = str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789")


def room_opts(**o):
    d = {"voice": num("voice_count", 4), "chat": num("chat_count", 2), "vname": get("voice_name") or "",
         "cname": get("chat_name") or "شات", "oname": get("owner_name") or "اونر"}
    for k, v in o.items():
        if v is None or str(v).strip() == "":
            continue
        if k in ("vname", "cname", "oname"):
            d[k] = str(v).strip()
        else:
            try:
                d[k] = int(str(v).translate(_AR_DIGITS).strip())
            except ValueError:
                raise ValueError("اكتب أعداد الرومات بالأرقام")
    d["voice"] = max(0, min(10, d["voice"]))
    d["chat"] = max(1, min(10, d["chat"]))
    return d


def _nm(base, n, total):
    return (f"{base} {n}" if total > 1 else base)[:100]


async def create_forum(guild, f, opts=None):
    o = opts or room_opts()
    name = f["name"]
    owner = guild.get_member(f["owner_id"]) or await guild.fetch_member(f["owner_id"])
    role = await guild.create_role(name=name, reason="forum approved")
    cat = await guild.create_category(name, overwrites={
        guild.default_role: P(view_channel=False),
        role: P(view_channel=True, connect=True, speak=True, send_messages=True, read_message_history=True),
        guild.me: P(view_channel=True, send_messages=True, manage_channels=True)})
    vbase = o["vname"] or name
    vperm = {guild.default_role: P(view_channel=True, connect=False),
             role: P(view_channel=True, connect=True, speak=True),
             guild.me: P(view_channel=True, connect=True, manage_channels=True)}
    for n in range(1, o["voice"] + 1):
        await guild.create_voice_channel(_nm(vbase, n, o["voice"]), category=cat, overwrites=vperm)
    chat = None
    for n in range(1, o["chat"] + 1):
        c = await guild.create_text_channel(_nm(o["cname"], n, o["chat"]), category=cat)
        chat = chat or c
    gch = await guild.create_text_channel("تجمع", category=cat)
    pch = await guild.create_text_channel("صور", category=cat)
    panel = await guild.create_text_channel(f"{o['oname']}-{name}"[:100], category=cat, overwrites={
        guild.default_role: P(view_channel=False), role: P(view_channel=False),
        owner: P(view_channel=True, read_message_history=True),
        guild.me: P(view_channel=True, send_messages=True, attach_files=True)})
    await owner.add_roles(role)
    q("UPDATE forums SET status='active',role_id=?,category_id=?,panel_id=?,chat_id=?,gather_id=?,photos_id=? WHERE id=?",
      (role.id, cat.id, panel.id, chat.id, gch.id, pch.id, f["id"]))
    q("INSERT OR REPLACE INTO members(forum_id,user_id,banned) VALUES(?,?,0)", (f["id"], owner.id))
    fresh = one("SELECT * FROM forums WHERE id=?", (f["id"],))
    await send_panel(guild, fresh)
    try:
        await send_gather_panel(guild, fresh)
    except (ValueError, discord.HTTPException):
        pass
    add_log(f["id"], "تم إنشاء المنتدى بواسطة الإدارة")


async def send_panel(guild, f):
    pn = guild.get_channel(f["panel_id"] or 0)
    if not pn:
        raise ValueError("روم اللوحة غير موجود")
    v = discord.ui.View(timeout=None)
    for a, *_ in PANEL_BUTTONS:
        v.add_item(PanelBtn(a, f["id"]))
    await send_card(pn, "panel", "لوحة تحكم المنتدى", f["name"], text="تحكم بمنتداك من الأزرار بالأسفل.",
                    content=f"<@{f['owner_id']}>", view=v)


async def send_gather_panel(guild, f):
    gc = guild.get_channel(f["gather_id"] or 0)
    if not gc:
        raise ValueError("روم التجمع غير موجود")
    await send_card(gc, "gpanel", "لوحة التجمعات", f["name"],
                    text="أعلن تجمع منتداك من الأزرار بالأسفل، ويتم منشن رتبة المنتدى.", view=GatherView())


async def ensure_rooms(guild, f):
    cat = guild.get_channel(f["category_id"] or 0)
    if not cat:
        raise ValueError("كاتيجوري المنتدى غير موجود")
    made = []
    for col, name in (("gather_id", "تجمع"), ("photos_id", "صور")):
        if not guild.get_channel(f[col] or 0):
            ch = await guild.create_text_channel(name, category=cat)
            q(f"UPDATE forums SET {col}=? WHERE id=?", (ch.id, f["id"]))
            made.append(name)
            if col == "gather_id":
                try:
                    await send_gather_panel(guild, one("SELECT * FROM forums WHERE id=?", (f["id"],)))
                except (ValueError, discord.HTTPException):
                    pass
    if made:
        add_log(f["id"], "إضافة رومات: " + "، ".join(made))
    return made


async def delete_forum(guild, f):
    cat = guild.get_channel(f["category_id"] or 0)
    if cat:
        for c in cat.channels:
            await c.delete()
        await cat.delete()
    role = guild.get_role(f["role_id"] or 0)
    if role:
        await role.delete()
    q("DELETE FROM forums WHERE id=?", (f["id"],))
    q("DELETE FROM members WHERE forum_id=?", (f["id"],))
    q("DELETE FROM warnings WHERE forum_id=?", (f["id"],))


async def rename_forum(guild, f, new):
    q("UPDATE forums SET name=? WHERE id=?", (new, f["id"]))
    role = guild.get_role(f["role_id"] or 0)
    cat = guild.get_channel(f["category_id"] or 0)
    pn = guild.get_channel(f["panel_id"] or 0)
    if role:
        await role.edit(name=new)
    if cat:
        await cat.edit(name=new)
        for vc in cat.voice_channels:
            if vc.name.startswith(f["name"]):
                await vc.edit(name=(new + vc.name[len(f["name"]):])[:100])
    if pn:
        await pn.edit(name=f"اونر-{new}"[:100])
    add_log(f["id"], f"تغيير الاسم من {f['name']} إلى {new}")


# ───────────── قواعد الأعضاء ─────────────
DAY = 86400


def plain(t):
    return re.sub(r"<t:(\d+):R>", lambda m: time.strftime("%Y-%m-%d %H:%M", time.localtime(int(m[1]))), t)


def name_taken(name, exclude=0):
    return bool(one("SELECT id FROM forums WHERE lower(name)=lower(?) AND status IN ('pending','active') AND id!=?",
                    (name.strip(), exclude)))


def joined_forums(uid):
    return allrows("SELECT f.* FROM forums f JOIN members m ON m.forum_id=f.id "
                   "WHERE m.user_id=? AND m.banned=0 AND f.status='active'", (uid,))


def check_join(uid, fid=None, skip_pending=0):
    c = one("SELECT * FROM cooldowns WHERE user_id=?", (uid,))
    if c and c["until"] > time.time() and c["from_forum"] != fid:
        return f"لازم تنتظر <t:{c['until']}:R> قبل ما تدخل أو تقدم على منتدى ثاني."
    n = len([f for f in joined_forums(uid) if f["id"] != fid])
    if fid is None:
        n += one("SELECT COUNT(*) c FROM forums WHERE owner_id=? AND status='pending' AND id!=?",
                 (uid, skip_pending))["c"]
    mx = int(get("max_forums") or 1)
    if n >= mx:
        return f"مرتبط بـ {n} منتدى/طلب والحد الأقصى {mx}. لازم أونر منتداك الحالي يطلّعه أول."
    return None


def role_of(uid, f):
    if uid == f["owner_id"]:
        return "owner"
    m = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], uid))
    return "deputy" if m and m["deputy"] and not m["banned"] else None


def can_manage(user, f, owner_only=False):
    if is_admin(user):
        return True
    r = role_of(user.id, f)
    return r == "owner" or (r == "deputy" and not owner_only)


async def add_member(guild, f, uid):
    try:
        m = guild.get_member(uid) or await guild.fetch_member(uid)
    except discord.NotFound:
        raise ValueError("العضو مو موجود بالسيرفر")
    role = guild.get_role(f["role_id"] or 0)
    if not role:
        raise ValueError("رتبة المنتدى غير موجودة")
    await m.add_roles(role)
    cat = guild.get_channel(f["category_id"] or 0)
    if cat:
        await cat.set_permissions(m, overwrite=None)
    q("INSERT OR REPLACE INTO members(forum_id,user_id,banned,deputy) VALUES(?,?,0,0)", (f["id"], uid))
    add_log(f["id"], f"انضم {m} ({uid})")
    ch = guild.get_channel(f["chat_id"] or 0)
    if ch:
        await ch.send(f"{em('users')} {m.mention} انضم للمنتدى")
    return m


async def remove_member(guild, f, uid, ban=False):
    m = guild.get_member(uid)
    t = m or discord.Object(uid)
    role = guild.get_role(f["role_id"] or 0)
    cat = guild.get_channel(f["category_id"] or 0)
    pn = guild.get_channel(f["panel_id"] or 0)
    if m and role and role in m.roles:
        await m.remove_roles(role)
    if cat:
        if ban:
            await cat.set_permissions(t, view_channel=False)
        else:
            await cat.set_permissions(t, overwrite=None)
    if pn:
        await pn.set_permissions(t, overwrite=None)
    if ban:
        q("INSERT OR REPLACE INTO members(forum_id,user_id,banned,deputy) VALUES(?,?,1,0)", (f["id"], uid))
    else:
        q("DELETE FROM members WHERE forum_id=? AND user_id=?", (f["id"], uid))
    days = int(get("cooldown_days") if get("cooldown_days") is not None else 3)
    until = int(time.time()) + days * DAY
    if days > 0:
        q("INSERT OR REPLACE INTO cooldowns(user_id,until,from_forum) VALUES(?,?,?)", (uid, until, f["id"]))
    add_log(f["id"], f"{'باند' if ban else 'إخراج'} للعضو {m or uid} ({uid})")
    try:
        u = m or await bot.fetch_user(uid)
        await send_card(u, "ban" if ban else "kick", "تم حظرك من المنتدى" if ban else "تم إخراجك من المنتدى", f["name"],
                        text=f"تقدر تدخل منتدى ثاني بعد <t:{until}:R>." if days > 0 else None, color=0xB33A3A)
    except discord.HTTPException:
        pass


async def unban_member(guild, f, uid):
    r = one("SELECT * FROM members WHERE forum_id=? AND user_id=? AND banned=1", (f["id"], uid))
    if not r:
        raise ValueError("العضو مو محظور")
    cat = guild.get_channel(f["category_id"] or 0)
    if cat:
        await cat.set_permissions(guild.get_member(uid) or discord.Object(uid), overwrite=None)
    q("DELETE FROM members WHERE forum_id=? AND user_id=?", (f["id"], uid))
    add_log(f["id"], f"فك باند ({uid})")


async def transfer_owner(guild, f, new_uid):
    r = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], new_uid))
    if new_uid == f["owner_id"]:
        raise ValueError("هو الأونر أصلاً")
    if not r or r["banned"]:
        raise ValueError("لازم يكون عضو بالمنتدى")
    old = f["owner_id"]
    q("UPDATE forums SET owner_id=? WHERE id=?", (new_uid, f["id"]))
    q("UPDATE members SET deputy=0 WHERE forum_id=? AND user_id=?", (f["id"], new_uid))
    pn = guild.get_channel(f["panel_id"] or 0)
    if pn:
        await pn.set_permissions(guild.get_member(new_uid) or discord.Object(new_uid),
                                 view_channel=True, read_message_history=True)
        await pn.set_permissions(guild.get_member(old) or discord.Object(old), overwrite=None)
    if not guild.get_member(old):
        q("DELETE FROM members WHERE forum_id=? AND user_id=?", (f["id"], old))
    add_log(f["id"], f"نقل ملكية المنتدى من {old} إلى {new_uid}")
    try:
        await send_panel(guild, one("SELECT * FROM forums WHERE id=?", (f["id"],)))
    except (ValueError, discord.HTTPException):
        pass


async def set_deputy(guild, f, uid, on):
    r = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], uid))
    if uid == f["owner_id"] or not r or r["banned"]:
        raise ValueError("لازم يكون عضو بالمنتدى")
    if on and not r["deputy"]:
        cnt = one("SELECT COUNT(*) c FROM members WHERE forum_id=? AND deputy=1", (f["id"],))["c"]
        mx = int(get("max_deputies") or 2)
        if cnt >= mx:
            raise ValueError(f"وصلت الحد الأقصى للنواب ({mx})")
    q("UPDATE members SET deputy=? WHERE forum_id=? AND user_id=?", (1 if on else 0, f["id"], uid))
    pn = guild.get_channel(f["panel_id"] or 0)
    t = guild.get_member(uid) or discord.Object(uid)
    if pn:
        if on:
            await pn.set_permissions(t, view_channel=True, read_message_history=True)
        else:
            await pn.set_permissions(t, overwrite=None)
    add_log(f["id"], f"{'تعيين' if on else 'إزالة'} نائب ({uid})")


async def post_event(guild, f, name, prize):
    ch = guild.get_channel(f["chat_id"] or 0)
    if not ch:
        raise ValueError("شات المنتدى غير موجود")
    role = guild.get_role(f["role_id"] or 0)
    await send_card(ch, "event", "فعالية جديدة", name, f"الجائزة: {prize}",
                    fields=[("الفعالية", name, True), ("الجائزة", prize, True)],
                    content=role.mention if role else None, allowed_mentions=discord.AllowedMentions(roles=True))
    add_log(f["id"], f"فعالية: {name} | الجائزة: {prize}")


# ───────────── طلب منتدى ─────────────
class ApplyModal(discord.ui.Modal, title="تقديم منتدى"):
    name = discord.ui.TextInput(label="اسم المنتدى", max_length=40)
    size = discord.ui.TextInput(label="عدد أعضاء المنتدى", max_length=6)
    tiktok = discord.ui.TextInput(label="يوزر التيك توك", max_length=40)

    async def on_submit(self, i):
        ch = i.guild.get_channel(int(get("requests_ch") or 0))
        if not ch:
            return await i.response.send_message("الإدارة ما ضبطت روم الطلبات.", ephemeral=True)
        raw = str(self.size).translate(str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789")).strip()
        if not raw.isdigit():
            return await i.response.send_message("اكتب عدد الأعضاء بالأرقام فقط.", ephemeral=True)
        name = str(self.name).strip()
        if name_taken(name):
            return await i.response.send_message(f"{em('cross')} اسم المنتدى مستخدم، اختر اسم ثاني.", ephemeral=True)
        err = check_join(i.user.id)
        if err:
            return await i.response.send_message(f"{em('cross')} " + err, ephemeral=True)
        count, minimum = int(raw), int(get("min_members") or 5)
        if count < minimum:
            q("INSERT INTO forums(name,owner_id,tiktok,size,status) VALUES(?,?,?,?,'rejected')",
              (name, i.user.id, str(self.tiktok), raw))
            await send_card(ch, "no", "طلب مرفوض تلقائياً", name, f"العدد {count}  •  الحد الأدنى {minimum}",
                            text=f"{i.user.mention} قدّم طلب بعدد أعضاء أقل من الحد.", color=0xB33A3A)
            return await i.response.send_message(
                f"{em('cross')} تم رفض الطلب: لازم يكون عدد أعضاء المنتدى {minimum} على الأقل (عدد منتداك {count}).",
                ephemeral=True)
        fid = q("INSERT INTO forums(name,owner_id,tiktok,size,status) VALUES(?,?,?,?,'pending')",
                (name, i.user.id, str(self.tiktok), raw)).lastrowid
        v = discord.ui.View(timeout=None)
        v.add_item(RqBtn("ok", fid))
        v.add_item(RqBtn("no", fid))
        await send_card(ch, "request", "طلب منتدى جديد", name, f"العدد: {raw}  •  تيك توك: {self.tiktok}",
                        fields=[("الاسم", name, True), ("العدد", raw, True), ("التيك توك", str(self.tiktok), True),
                                ("المقدّم", i.user.mention, False)], view=v)
        await i.response.send_message(f"تم إرسال طلبك للإدارة {em('check')}", ephemeral=True)


class ApplyView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)
        self.children[0].emoji = emo("forum")

    @discord.ui.button(label="تقديم منتدى", style=discord.ButtonStyle.primary, custom_id="apply")
    async def b(self, i, _):
        await i.response.send_modal(ApplyModal())


async def process_request(guild, f, accept, opts=None):
    note = ""
    if accept:
        err = check_join(f["owner_id"], None, skip_pending=f["id"])
        if err or name_taken(f["name"], f["id"]):
            accept, note = False, plain(err or "اسم المنتدى مستخدم")
    if accept:
        await create_forum(guild, f, opts)
    else:
        q("UPDATE forums SET status='rejected' WHERE id=?", (f["id"],))
    try:
        u = await bot.fetch_user(f["owner_id"])
        await send_card(u, "ok" if accept else "no", "تم قبول طلبك" if accept else "تم رفض طلبك", f["name"],
                        text=note or None, color=0x3A9B5C if accept else 0xB33A3A)
    except discord.HTTPException:
        pass
    return accept, note


class RqBtn(discord.ui.DynamicItem[discord.ui.Button], template=r"rq:(?P<a>ok|no):(?P<f>\d+)"):
    def __init__(self, a, f):
        ok = a == "ok"
        super().__init__(discord.ui.Button(label="قبول" if ok else "رفض", emoji=emo("check" if ok else "cross"),
                                           style=discord.ButtonStyle.success if ok else discord.ButtonStyle.danger,
                                           custom_id=f"rq:{a}:{f}"))
        self.a, self.f = a, int(f)

    @classmethod
    async def from_custom_id(cls, i, item, m, /):
        return cls(m["a"], m["f"])

    async def callback(self, i):
        if not is_admin(i.user):
            return await i.response.send_message("للإدارة فقط.", ephemeral=True)
        f = one("SELECT * FROM forums WHERE id=?", (self.f,))
        if not f or f["status"] != "pending":
            return await i.response.send_message("الطلب تمت معالجته.", ephemeral=True)
        if self.a == "ok":
            return await i.response.send_modal(AcceptModal(f, i.message))
        await i.response.defer()
        ok, note = await process_request(i.guild, f, False)
        await finish_request(i.message, i.user, ok, note)


async def finish_request(msg, user, ok, note):
    e = msg.embeds[0]
    e.color = 0x3A9B5C if ok else 0xB33A3A
    e.set_footer(text=f"مقبول بواسطة {user}" if ok else f"مرفوض بواسطة {user}" + (f" (تلقائي: {note})" if note else ""))
    await msg.edit(embed=e, view=None)


class AcceptModal(discord.ui.Modal, title="قبول المنتدى وتحديد الرومات"):
    vc = discord.ui.TextInput(label="عدد الرومات الصوتية (0-10)", max_length=2)
    cc = discord.ui.TextInput(label="عدد رومات الشات (1-10)", max_length=2)
    vn = discord.ui.TextInput(label="اسم الصوتي (فاضي = اسم المنتدى)", max_length=30, required=False)
    cn = discord.ui.TextInput(label="اسم رومات الشات", max_length=30)
    ow = discord.ui.TextInput(label="اسم روم الأونر", max_length=30)

    def __init__(self, f, msg):
        super().__init__()
        self.f, self.msg = f, msg
        o = room_opts()
        self.vc.default, self.cc.default = str(o["voice"]), str(o["chat"])
        self.vn.default, self.cn.default, self.ow.default = o["vname"], o["cname"], o["oname"]

    async def on_submit(self, i):
        try:
            o = room_opts(voice=str(self.vc), chat=str(self.cc), vname=str(self.vn), cname=str(self.cn), oname=str(self.ow))
        except ValueError as ex:
            return await i.response.send_message(f"{em('cross')} {ex}", ephemeral=True)
        await i.response.defer(ephemeral=True)
        f = one("SELECT * FROM forums WHERE id=?", (self.f["id"],))
        if not f or f["status"] != "pending":
            return await i.followup.send("الطلب تمت معالجته.", ephemeral=True)
        ok, note = await process_request(i.guild, f, True, o)
        await finish_request(self.msg, i.user, ok, note)
        await i.followup.send(f"{'تم قبول المنتدى' if ok else 'تم رفض الطلب'} {em('check' if ok else 'cross')}", ephemeral=True)


# ───────────── لوحة الأونر ─────────────
class PickUser(discord.ui.View):
    def __init__(self, cb):
        super().__init__(timeout=120)
        self.cb = cb

    @discord.ui.select(cls=discord.ui.UserSelect, placeholder="اختر العضو")
    async def s(self, i, sel):
        await self.cb(i, sel.values[0])


class RenameModal(discord.ui.Modal, title="تغيير اسم المنتدى"):
    n = discord.ui.TextInput(label="الاسم الجديد", max_length=40)

    def __init__(self, f):
        super().__init__()
        self.f = f
        self.n.default = f["name"]

    async def on_submit(self, i):
        new = str(self.n).strip()
        if name_taken(new, self.f["id"]):
            return await i.response.send_message(f"{em('cross')} الاسم مستخدم.", ephemeral=True)
        await i.response.defer(ephemeral=True)
        await rename_forum(i.guild, self.f, new)
        await i.followup.send(f"تم تغيير الاسم {em('check')}", ephemeral=True)


class EventModal(discord.ui.Modal, title="فعالية جديدة"):
    n = discord.ui.TextInput(label="ما هي الفعالية؟", max_length=100)
    p = discord.ui.TextInput(label="الجائزة", max_length=100)

    def __init__(self, f):
        super().__init__()
        self.f = f

    async def on_submit(self, i):
        try:
            await post_event(i.guild, self.f, str(self.n), str(self.p))
        except ValueError as ex:
            return await i.response.send_message(f"{em('cross')} {ex}", ephemeral=True)
        await i.response.send_message(f"تم نشر الفعالية {em('check')}", ephemeral=True)


class WarnModal(discord.ui.Modal, title="تحذير عضو"):
    r = discord.ui.TextInput(label="سبب التحذير", style=discord.TextStyle.paragraph, max_length=300)

    def __init__(self, f, user):
        super().__init__()
        self.f, self.user = f, user

    async def on_submit(self, i):
        await i.response.defer(ephemeral=True)
        f, u = self.f, self.user
        q("INSERT INTO warnings(forum_id,user_id,reason,ts) VALUES(?,?,?,?)", (f["id"], u.id, str(self.r), int(time.time())))
        n = one("SELECT COUNT(*) c FROM warnings WHERE forum_id=? AND user_id=?", (f["id"], u.id))["c"]
        mx = num("max_warns", 3)
        add_log(f["id"], f"تحذير {n}/{mx or '∞'} لـ {u} ({u.id}): {self.r}")
        try:
            await send_card(u, "warn", "وصلك تحذير", f["name"], f"{n}/{mx or '∞'}", text=f"السبب: {self.r}", color=0xE6AC4F)
        except discord.HTTPException:
            pass
        if mx and n >= mx:
            q("DELETE FROM warnings WHERE forum_id=? AND user_id=?", (f["id"], u.id))
            await remove_member(i.guild, f, u.id)
            add_log(f["id"], f"إخراج تلقائي بعد {n} تحذيرات ({u.id})")
            msg = f"وصل {u.mention} إلى {n} تحذيرات وتم إخراجه تلقائياً {em('check')}"
        else:
            msg = f"تم تحذير {u.mention} ({n}/{mx or '∞'}) {em('check')}"
        await i.followup.send(msg, ephemeral=True)


def protect(f, actor, uid):
    if uid == f["owner_id"]:
        return "ما تقدر تسوي هذا للأونر."
    r = one("SELECT deputy FROM members WHERE forum_id=? AND user_id=?", (f["id"], uid))
    if r and r["deputy"] and not (actor.id == f["owner_id"] or is_admin(actor)):
        return "بس الأونر يتحكم بالنواب."
    return None


async def invite_cb(i, f, user):
    m = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], user.id))
    if user.bot:
        return await i.response.edit_message(content="ما تقدر تدعو بوت.", view=None)
    if m and m["banned"]:
        return await i.response.edit_message(content="العضو محظور من المنتدى (فك الباند أول).", view=None)
    if m:
        return await i.response.edit_message(content="العضو بالمنتدى أصلاً.", view=None)
    err = check_join(user.id, f["id"])
    if err:
        return await i.response.edit_message(content=f"{em('cross')} " + err, view=None)
    v = discord.ui.View(timeout=None)
    v.add_item(IvBtn("ok", f["id"]))
    v.add_item(IvBtn("no", f["id"]))
    try:
        await send_card(user, "invite", "دعوة دخول", f["name"], text=f"منتدى **{f['name']}** أرسل لك دعوة للانضمام.", view=v)
    except discord.HTTPException:
        return await i.response.edit_message(content="ما قدرت أرسل له خاص (الخاص مقفل).", view=None)
    add_log(f["id"], f"دعوة أُرسلت إلى {user} ({user.id})")
    await i.response.edit_message(content=f"تم إرسال الدعوة {em('check')}", view=None)


async def _remove(i, f, user, ban):
    err = protect(f, i.user, user.id)
    if err:
        return await i.response.edit_message(content=err, view=None)
    m = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], user.id))
    if not ban and not m:
        return await i.response.edit_message(content="العضو مو بالمنتدى.", view=None)
    await i.response.defer()
    await remove_member(i.guild, f, user.id, ban=ban)
    await i.edit_original_response(content=f"تم {'حظر' if ban else 'إخراج'} {user.mention} {em('check')}", view=None)


async def kick_cb(i, f, user):
    await _remove(i, f, user, False)


async def ban_cb(i, f, user):
    await _remove(i, f, user, True)


async def unban_cb(i, f, user):
    await i.response.defer()
    try:
        await unban_member(i.guild, f, user.id)
        msg = f"تم فك الباند عن {user.mention} {em('check')}"
    except ValueError as ex:
        msg = f"{em('cross')} {ex}"
    await i.edit_original_response(content=msg, view=None)


async def warn_cb(i, f, user):
    err = protect(f, i.user, user.id)
    m = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], user.id))
    if not err and (not m or m["banned"]):
        err = "العضو مو بالمنتدى."
    if err:
        return await i.response.edit_message(content=err, view=None)
    await i.response.send_modal(WarnModal(f, user))


async def deputy_cb(i, f, user):
    await i.response.defer()
    r = one("SELECT deputy FROM members WHERE forum_id=? AND user_id=?", (f["id"], user.id))
    on = not (r and r["deputy"])
    try:
        await set_deputy(i.guild, f, user.id, on)
        msg = f"{'تم تعيين' if on else 'تمت إزالة'} {user.mention} {'نائب' if on else 'من النواب'} {em('check')}"
    except ValueError as ex:
        msg = f"{em('cross')} {ex}"
    await i.edit_original_response(content=msg, view=None)


class PanelBtn(discord.ui.DynamicItem[discord.ui.Button], template=r"fp:(?P<a>\w+):(?P<f>\d+)"):
    def __init__(self, a, f):
        label, icon = {x: (y, z) for x, y, z in PANEL_BUTTONS}.get(a, (a, None))
        super().__init__(discord.ui.Button(label=label, emoji=emo(icon) if icon else None,
                                           style=discord.ButtonStyle.secondary, custom_id=f"fp:{a}:{f}"))
        self.a, self.f = a, int(f)

    @classmethod
    async def from_custom_id(cls, i, item, m, /):
        return cls(m["a"], m["f"])

    async def callback(self, i):
        f = one("SELECT * FROM forums WHERE id=?", (self.f,))
        a = self.a
        if not f:
            return await i.response.send_message("المنتدى غير موجود.", ephemeral=True)
        if not can_manage(i.user, f, a in OWNER_ONLY):
            return await i.response.send_message("للأونر فقط." if a in OWNER_ONLY else "للأونر والنواب فقط.",
                                                 ephemeral=True)
        if a == "rename":
            return await i.response.send_modal(RenameModal(f))
        if a == "event":
            return await i.response.send_modal(EventModal(f))
        if a == "log":
            rows = allrows("SELECT * FROM logs WHERE forum_id=? ORDER BY id DESC LIMIT 20", (f["id"],))
            txt = "\n".join(f"<t:{r['ts']}:R> {r['text']}" for r in rows) or "لا يوجد سجل."
            return await i.response.send_message(embed=discord.Embed(title="لوق المنتدى", description=txt, color=COLOR),
                                                 ephemeral=True)
        cb = {"invite": invite_cb, "kick": kick_cb, "ban": ban_cb, "unban": unban_cb, "warn": warn_cb,
              "deputy": deputy_cb}.get(a)
        if not cb:
            return await i.response.send_message("زر غير معروف.", ephemeral=True)
        await i.response.send_message("اختر العضو:", view=PickUser(lambda ii, u: cb(ii, f, u)), ephemeral=True)


class IvBtn(discord.ui.DynamicItem[discord.ui.Button], template=r"iv:(?P<a>ok|no):(?P<f>\d+)"):
    def __init__(self, a, f):
        ok = a == "ok"
        super().__init__(discord.ui.Button(label="قبول" if ok else "رفض", emoji=emo("check" if ok else "cross"),
                                           style=discord.ButtonStyle.success if ok else discord.ButtonStyle.danger,
                                           custom_id=f"iv:{a}:{f}"))
        self.a, self.f = a, int(f)

    @classmethod
    async def from_custom_id(cls, i, item, m, /):
        return cls(m["a"], m["f"])

    async def callback(self, i):
        f = one("SELECT * FROM forums WHERE id=?", (self.f,))
        if not f or f["status"] != "active":
            return await i.response.edit_message(content="المنتدى غير موجود.", view=None)
        if self.a == "no":
            add_log(f["id"], f"{i.user} رفض الدعوة")
            return await i.response.edit_message(content="تم رفض الدعوة.", view=None)
        g = i.client.get_guild(GUILD_ID)
        mm = one("SELECT banned FROM members WHERE forum_id=? AND user_id=?", (f["id"], i.user.id))
        if mm and mm["banned"]:
            return await i.response.edit_message(content="أنت محظور من هذا المنتدى.", view=None)
        err = check_join(i.user.id, f["id"])
        if err:
            return await i.response.edit_message(content=f"{em('cross')} " + err, view=None)
        await i.response.defer()
        try:
            await add_member(g, f, i.user.id)
        except ValueError as ex:
            return await i.edit_original_response(content=f"{em('cross')} {ex}", view=None)
        await i.edit_original_response(content=f"تم دخولك منتدى **{f['name']}** {em('check')}", view=None)


# ───────────── التجمعات ─────────────
def can_gather(m):
    if is_admin(m) or has_role(m, "gather_manager_role"):
        return True
    return any(role_of(m.id, f) for f in joined_forums(m.id))


def can_public_gather(m):
    return get("pub_everyone") == "1" or is_admin(m) or has_role(m, "gather_manager_role")


async def end_gathering(guild, g):
    q("UPDATE gatherings SET active=0 WHERE id=?", (g["id"],))
    ch = guild.get_channel(g["channel_id"] or 0)
    if ch:
        try:
            m = await ch.fetch_message(g["message_id"])
            e = m.embeds[0]
            e.color = 0xB33A3A
            e.set_image(url="attachment://gend.png")
            await m.edit(content=None, embed=e,
                         attachments=[await acard("gend", "انتهى التجمع", g["server"], f"الرمز: {g['symbol']}")])
        except (discord.HTTPException, IndexError):
            pass
    fo = one("SELECT * FROM forums WHERE id=?", (g["forum_id"],)) if g["forum_id"] else None
    gc = guild.get_channel(fo["gather_id"] or 0) if fo else None
    if gc and gc.id != g["channel_id"]:
        try:
            await send_card(gc, "gend", "انتهى التجمع", g["server"], f"الرمز: {g['symbol']}", color=0xB33A3A)
        except discord.HTTPException:
            pass
    ph = guild.get_channel(int(get("photos_ch") or DEFAULT_PHOTOS_CH))
    if ph:
        try:
            await send_card(ph, "photos", "صور التجمع", g["server"], f"الرمز: {g['symbol']}",
                            text="انتهى التجمع، شاركوا صوركم هنا.")
        except discord.HTTPException:
            pass


# ── تجمع المنتدى (لوحته داخل روم "تجمع" الخاص بالمنتدى، ويمنشن رتبة المنتدى) ──
class GatherModal(discord.ui.Modal, title="تجمع جديد"):
    server = discord.ui.TextInput(label="اسم السيرفر", max_length=60)
    symbol = discord.ui.TextInput(label="رمز السيرفر", max_length=20)

    async def on_submit(self, i):
        await i.response.defer(ephemeral=True)
        forums_ = [f for f in joined_forums(i.user.id) if f["role_id"]]
        roles = [r for r in (i.guild.get_role(f["role_id"]) for f in forums_) if r]
        if not roles:
            r = i.guild.get_role(int(get("gather_ping_role") or 0))
            roles = [r] if r else []
        dest = i.guild.get_channel(int(get("notices_ch") or 0)) or i.channel
        server, symbol = str(self.server), str(self.symbol)
        fields = [("السيرفر", server, True), ("الرمز", symbol, True),
                  ("المنتدى", "، ".join(f["name"] for f in forums_) or "—", True), ("المسؤول", i.user.mention, False)]
        msg = await send_card(dest, "gnew", "تجمع جديد", server, f"الرمز: {symbol}", color=0x3A9B5C, fields=fields,
                              content=" ".join(r.mention for r in roles) or None,
                              allowed_mentions=discord.AllowedMentions(roles=True))
        for f_ in forums_:
            gc = i.guild.get_channel(f_["gather_id"] or 0)
            if gc and gc.id != dest.id:
                try:
                    await send_card(gc, "gnew", "تجمع جديد", server, f"الرمز: {symbol}", color=0x3A9B5C,
                                    fields=[("السيرفر", server, True), ("الرمز", symbol, True), ("المسؤول", i.user.mention, False)])
                except discord.HTTPException:
                    pass
        q("INSERT INTO gatherings(user_id,server,symbol,channel_id,message_id,forum_id,pub) VALUES(?,?,?,?,?,?,0)",
          (i.user.id, server, symbol, dest.id, msg.id, forums_[0]["id"] if forums_ else None))
        await i.followup.send(f"تم إعلان التجمع {em('check')}", ephemeral=True)


class GatherView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)
        self.children[0].emoji = emo("megaphone")
        self.children[1].emoji = emo("stop")

    @discord.ui.button(label="تجمع", style=discord.ButtonStyle.success, custom_id="g:start")
    async def start(self, i, _):
        if not can_gather(i.user):
            return await i.response.send_message("لمسؤول التجمعات وأونر المنتدى ونوابه فقط.", ephemeral=True)
        await i.response.send_modal(GatherModal())

    @discord.ui.button(label="انتهى تجمع", style=discord.ButtonStyle.danger, custom_id="g:end")
    async def end(self, i, _):
        if not can_gather(i.user):
            return await i.response.send_message("لمسؤول التجمعات وأونر المنتدى ونوابه فقط.", ephemeral=True)
        rows = allrows("SELECT * FROM gatherings WHERE user_id=? AND active=1 AND COALESCE(pub,0)=0", (i.user.id,))
        if not rows:
            return await i.response.send_message("ما عندك تجمع شغال.", ephemeral=True)
        await i.response.defer(ephemeral=True)
        for g in rows:
            await end_gathering(i.guild, g)
        await i.followup.send(f"تم إنهاء التجمع {em('check')}", ephemeral=True)


# ── نظام إنشاء التجمع العام (مو مرتبط بمنتدى، المنشن يُحدد من الداشبورد) ──
async def send_public_panel(guild, channel=None):
    ch = guild.get_channel(int(get("pub_gather_ch") or 0)) or channel
    if not ch:
        raise ValueError("حدد روم لوحة التجمع العام من الإعدادات أول")
    await send_card(ch, "gpanel", "إنشاء تجمع", "أعلن تجمعك بسهولة", text="اضغط الزر وأدخل اسم السيرفر والرمز.",
                    view=PublicGatherView())


class PublicGatherModal(discord.ui.Modal, title="إنشاء تجمع"):
    server = discord.ui.TextInput(label="اسم السيرفر", max_length=60)
    symbol = discord.ui.TextInput(label="رمز السيرفر", max_length=20)

    async def on_submit(self, i):
        await i.response.defer(ephemeral=True)
        server, symbol = str(self.server), str(self.symbol)
        content, allowed = None, discord.AllowedMentions.none()
        if get("pub_mention") == "1":
            r = i.guild.get_role(int(get("pub_role") or 0))
            if r:
                content, allowed = r.mention, discord.AllowedMentions(roles=True)
        msg = await send_card(i.channel, "gnew", "تجمع جديد", server, f"الرمز: {symbol}", color=0x3A9B5C,
                              fields=[("السيرفر", server, True), ("الرمز", symbol, True), ("المسؤول", i.user.mention, False)],
                              content=content, allowed_mentions=allowed)
        q("INSERT INTO gatherings(user_id,server,symbol,channel_id,message_id,pub) VALUES(?,?,?,?,?,1)",
          (i.user.id, server, symbol, i.channel.id, msg.id))
        await i.followup.send(f"تم إنشاء التجمع {em('check')}", ephemeral=True)


class PublicGatherView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)
        self.children[0].emoji = emo("megaphone")
        self.children[1].emoji = emo("stop")

    @discord.ui.button(label="إنشاء تجمع", style=discord.ButtonStyle.success, custom_id="pg:start")
    async def start(self, i, _):
        if not can_public_gather(i.user):
            return await i.response.send_message("إنشاء التجمع لمسؤولي التجمعات فقط.", ephemeral=True)
        await i.response.send_modal(PublicGatherModal())

    @discord.ui.button(label="إنهاء التجمع", style=discord.ButtonStyle.danger, custom_id="pg:end")
    async def end(self, i, _):
        if not can_public_gather(i.user):
            return await i.response.send_message("إنهاء التجمع لمسؤولي التجمعات فقط.", ephemeral=True)
        rows = allrows("SELECT * FROM gatherings WHERE user_id=? AND active=1 AND pub=1", (i.user.id,))
        if not rows:
            return await i.response.send_message("ما عندك تجمع شغال.", ephemeral=True)
        await i.response.defer(ephemeral=True)
        for g in rows:
            await end_gathering(i.guild, g)
        await i.followup.send(f"تم إنهاء التجمع {em('check')}", ephemeral=True)


# ───────────── البوت والأوامر ─────────────
class Bot(commands.Bot):
    def __init__(self):
        it = discord.Intents.default()
        it.members = True
        it.message_content = True
        super().__init__(command_prefix="!", intents=it)

    async def setup_hook(self):
        self.add_dynamic_items(RqBtn, PanelBtn, IvBtn)
        self.add_view(ApplyView())
        self.add_view(GatherView())
        self.add_view(PublicGatherView())
        runner = web.AppRunner(make_web())
        await runner.setup()
        await web.TCPSite(runner, "0.0.0.0", PORT).start()

    async def on_ready(self):
        global GUILD_ID
        if not self.get_guild(GUILD_ID):
            print(f"[تنبيه] GUILD_ID={GUILD_ID} مو من سيرفرات البوت. السيرفرات: {[(x.name, x.id) for x in self.guilds]}")
            if len(self.guilds) == 1:
                GUILD_ID = self.guilds[0].id
                print(f"[OK] تم استخدام السيرفر الوحيد تلقائياً: {GUILD_ID}")
        if not getattr(self, "_emoji_task", None):
            self._emoji_task = asyncio.create_task(load_emojis())
        if getattr(self, "_synced", False) or not self.get_guild(GUILD_ID):
            return
        g = discord.Object(GUILD_ID)
        self.tree.copy_global_to(guild=g)
        try:
            await self.tree.sync(guild=g)
            self._synced = True
            print("[OK] تم تسجيل الأوامر")
        except discord.Forbidden:
            print("[خطأ] Missing Access: أعد إضافة البوت بصلاحية applications.commands")

    async def on_message(self, message):
        if message.author.bot or not message.guild or message.guild.id != GUILD_ID:
            return
        f = one("SELECT * FROM forums WHERE photos_id=?", (message.channel.id,))
        if not f:
            return
        target = message.guild.get_channel(int(get("photos_ch") or DEFAULT_PHOTOS_CH))
        if not target or target.id == message.channel.id:
            return
        files = []
        for a in message.attachments[:10]:
            try:
                files.append(await a.to_file())
            except discord.HTTPException:
                pass
        if not files and not message.content.strip():
            return
        e = discord.Embed(description=message.content or None, color=COLOR)
        e.set_author(name=message.author.display_name, icon_url=message.author.display_avatar.url)
        e.set_footer(text=f["name"])
        try:
            await target.send(embed=e, files=files, allowed_mentions=discord.AllowedMentions.none())
        except discord.HTTPException as ex:
            print("[تنبيه] تعذر نقل رسالة الصور:", ex)

    async def on_member_remove(self, member):
        if member.guild.id != GUILD_ID:
            return
        rows = allrows("SELECT f.*, m.deputy AS dep FROM members m JOIN forums f ON f.id=m.forum_id "
                       "WHERE m.user_id=? AND m.banned=0 AND f.status='active'", (member.id,))
        for f in rows:
            if member.id == f["owner_id"]:
                ch = member.guild.get_channel(int(get("requests_ch") or 0))
                add_log(f["id"], f"الأونر {member} طلع من السيرفر")
                if ch:
                    await ch.send(embed=discord.Embed(
                        title=f"{em('warn')} أونر منتدى طلع من السيرفر", color=0xB33A3A,
                        description=f"المنتدى: **{f['name']}** (#{f['id']})\nانقل الملكية من الداشبورد."))
                continue
            q("DELETE FROM members WHERE forum_id=? AND user_id=?", (f["id"], member.id))
            pn = member.guild.get_channel(f["panel_id"] or 0)
            if f["dep"] and pn:
                await pn.set_permissions(discord.Object(member.id), overwrite=None)
            add_log(f["id"], f"{member} طلع من السيرفر وانشال من المنتدى")


bot = Bot()


def admin_only(i):
    return is_admin(i.user)


@bot.tree.command(name="setup", description="ضبط رومات ورتب البوت")
async def setup(i: discord.Interaction, requests: discord.TextChannel = None, notices: discord.TextChannel = None,
                photos: discord.TextChannel = None, gather_ping: discord.Role = None,
                gather_manager: discord.Role = None, admin: discord.Role = None,
                min_members: int = None, max_forums: int = None,
                cooldown_days: int = None, max_deputies: int = None, max_warns: int = None):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    for k, v in (("requests_ch", requests), ("notices_ch", notices), ("photos_ch", photos),
                 ("gather_ping_role", gather_ping), ("gather_manager_role", gather_manager), ("admin_role", admin)):
        if v:
            put(k, v.id)
    if min_members is not None:
        put("min_members", max(1, min_members))
    if max_forums is not None:
        put("max_forums", max(1, max_forums))
    if cooldown_days is not None:
        put("cooldown_days", max(0, cooldown_days))
    if max_deputies is not None:
        put("max_deputies", max(0, max_deputies))
    if max_warns is not None:
        put("max_warns", max(0, max_warns))
    await i.response.send_message(f"تم الحفظ {em('check')}", ephemeral=True)


@bot.tree.command(name="apply_panel", description="نشر زر تقديم المنتدى هنا")
async def apply_panel(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    await send_card(i.channel, "apply", "تقديم منتدى", "قدّم طلب إنشاء منتداك", text="اضغط الزر بالأسفل وعبّي البيانات.",
                    view=ApplyView())
    await i.response.send_message(f"تم {em('check')}", ephemeral=True)


@bot.tree.command(name="notice_panel", description="نشر لوحة التجمعات في روم الإشعارات")
async def notice_panel(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    ch = i.guild.get_channel(int(get("notices_ch") or 0)) or i.channel
    await send_card(ch, "gpanel", "لوحة التجمعات", "أعلن تجمعك أو أنهه", text="استخدم الأزرار بالأسفل.", view=GatherView())
    await i.response.send_message(f"تم {em('check')}", ephemeral=True)


@bot.tree.command(name="refresh_emojis", description="إعادة رفع إيموجيات البوت الخاصة")
async def refresh_emojis(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    await i.response.defer(ephemeral=True)
    await load_emojis(force=True)
    await i.followup.send(f"تم تحديث {len(EMO)} إيموجي {em('check')}", ephemeral=True)


@bot.tree.command(name="public_gather_panel", description="نشر لوحة نظام إنشاء التجمع العام")
async def public_gather_panel(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    try:
        await send_public_panel(i.guild, i.channel)
    except (ValueError, discord.HTTPException) as ex:
        return await i.response.send_message(f"{em('cross')} {ex}", ephemeral=True)
    await i.response.send_message(f"تم {em('check')}", ephemeral=True)


@bot.tree.command(name="backup", description="نسخة احتياطية من إعدادات وبيانات البوت")
async def backup(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    d = sqlite3.connect(os.path.join(DATA_DIR, "backup.db"))
    con.backup(d)
    d.close()
    await i.response.send_message("نسختك:", file=discord.File(os.path.join(DATA_DIR, "backup.db"), f"backup-{int(time.time())}.db"),
                                  ephemeral=True)


@bot.tree.command(name="restore", description="استرجاع نسخة احتياطية")
async def restore(i: discord.Interaction, file: discord.Attachment):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    await file.save(os.path.join(DATA_DIR, "restore.db"))
    try:
        s = sqlite3.connect(os.path.join(DATA_DIR, "restore.db"))
        s.execute("SELECT 1 FROM forums LIMIT 1")
        s.backup(con)
        s.close()
    except Exception as ex:
        return await i.response.send_message(f"ملف غير صالح: {ex}", ephemeral=True)
    await i.response.send_message(f"تم الاسترجاع {em('check')}", ephemeral=True)


@bot.tree.command(name="set_font", description="رفع خط (ttf/otf) للصور")
async def set_font(i: discord.Interaction, file: discord.Attachment):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    os.makedirs(os.path.dirname(FONT_PATH), exist_ok=True)
    await file.save(FONT_PATH)
    _FC.clear()
    await i.response.send_message(f"تم تغيير الخط {em('check')} (لازم يدعم الحروف العربية المتصلة)", ephemeral=True)


# ───────────── الداشبورد ─────────────
CSS = """
:root{--bg:#171310;--p1:#211c18;--p2:#2a241f;--line:#383029;--text:#f4ece6;--mut:#a99b8e;--acc:#c0a086;--acc2:#967a62;--ok:#4fb783;--bad:#e5645d;--warn:#e6ac4f}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:15px/1.6 "Segoe UI",Tahoma,system-ui,sans-serif}
a{color:var(--acc);text-decoration:none}
.app{display:flex;min-height:100vh}
.side{width:244px;background:var(--p1);border-left:1px solid var(--line);padding:18px 14px;position:sticky;top:0;height:100vh;display:flex;flex-direction:column;gap:6px}
.brand{display:flex;align-items:center;gap:10px;padding:6px 10px 16px;font-weight:700;font-size:17px}
.nav a{display:flex;align-items:center;gap:10px;padding:10px 12px;border-radius:10px;color:var(--mut);font-weight:600}
.nav a:hover{background:var(--p2);color:var(--text)}
.nav a.on{background:linear-gradient(135deg,var(--acc2),#7d654f);color:#fff}
.nav .n{margin-inline-start:auto;background:var(--bad);color:#fff;border-radius:99px;font-size:12px;padding:0 8px}
.side .out{margin-top:auto}
main{flex:1;padding:28px;max-width:1180px;width:100%;margin:auto;min-width:0}
h1{margin:0 0 4px;font-size:24px}.sub{color:var(--mut);margin:0 0 22px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:14px;margin-bottom:20px}
.stat{background:var(--p1);border:1px solid var(--line);border-radius:14px;padding:16px}
.stat span{color:var(--mut);font-size:13px}.stat b{display:block;font-size:28px;margin-top:2px}
.card{background:var(--p1);border:1px solid var(--line);border-radius:14px;padding:18px;margin-bottom:16px;overflow-x:auto}
.card h2{margin:0 0 12px;font-size:17px}.card h3{margin:0 0 10px;font-size:15px}
table{width:100%;border-collapse:collapse}
th{color:var(--mut);font-weight:600;font-size:13px}
th,td{padding:10px 8px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}
tr:last-child td{border-bottom:0}tbody tr:hover{background:#ffffff06}
input,select{background:var(--p2);color:var(--text);border:1px solid var(--line);border-radius:10px;padding:9px 12px;font:inherit;min-width:0}
input:focus,select:focus{outline:2px solid var(--acc2);border-color:transparent}
button{background:var(--acc2);color:#fff;border:0;border-radius:10px;padding:9px 14px;font:inherit;font-weight:600;cursor:pointer}
button:hover{filter:brightness(1.12)}
button.d{background:#8f3733}button.g{background:var(--p2);border:1px solid var(--line);color:var(--text)}
button.s{padding:5px 10px;font-size:13px}
.row{display:flex;gap:10px;flex-wrap:wrap;align-items:center}
.f2{display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:16px}
label{display:block;color:var(--mut);font-size:13px;margin:0 0 5px}
.fld input,.fld select{width:100%}.hint{color:var(--mut);font-size:12px;margin-top:4px}
.badge{display:inline-block;padding:2px 10px;border-radius:99px;font-size:12px;font-weight:700}
.b-ok{background:#4fb78322;color:var(--ok)}.b-bad{background:#e5645d22;color:var(--bad)}
.b-warn{background:#e6ac4f22;color:var(--warn)}.b-mut{background:#ffffff10;color:var(--mut)}
.tabs{display:flex;gap:8px;margin-bottom:16px;flex-wrap:wrap}
.tabs a{padding:7px 14px;border-radius:99px;background:var(--p1);border:1px solid var(--line);color:var(--mut);font-weight:600}
.tabs a.on{background:var(--acc2);color:#fff;border-color:transparent}
.toast{position:fixed;bottom:20px;left:20px;right:20px;max-width:420px;margin:auto;padding:12px 16px;border-radius:12px;background:var(--p2);border:1px solid var(--ok);z-index:9;box-shadow:0 10px 30px #0008}
.toast.err{border-color:var(--bad)}
.danger{border-color:#6b2c29}.empty{color:var(--mut);text-align:center;padding:22px}
.login{min-height:100vh;display:grid;place-items:center;padding:20px}
.login .card{width:100%;max-width:380px;text-align:center;padding:30px}
@media(max-width:820px){.app{display:block}.side{position:static;width:auto;height:auto;flex-direction:row;overflow-x:auto;border:0;border-bottom:1px solid var(--line);padding:10px;align-items:center}
.brand{padding:0 8px 0 14px}.brand span{display:none}.nav{display:flex;gap:4px}.nav a{white-space:nowrap;padding:8px 10px}.side .out{margin:0}main{padding:16px}}
"""

E = html.escape
STATUS = {"active": ("نشط", "ok"), "pending": ("قيد المراجعة", "warn"), "rejected": ("مرفوض", "bad")}
NAV = [("/", "chart", "نظرة عامة"), ("/requests", "inbox", "الطلبات"), ("/forums", "forum", "المنتديات"),
       ("/gatherings", "megaphone", "التجمعات"), ("/cooldowns", "clock", "الانتظار"), ("/logs", "log", "السجلات"),
       ("/settings", "gear", "الإعدادات")]


def ic(n, s=18):
    return f'<img src="/icon/{n}.png" width={s} height={s} style="vertical-align:-4px">'


def token():
    return hmac.new(DASH_PASS.encode(), b"dash", hashlib.sha256).hexdigest()


def logo_svg(h=34):
    p = "".join(f'<polygon points="{cx},{cy - R} {cx + R},{cy} {cx},{cy + R} {cx - R},{cy}" '
                f'fill="{"#cdbdb3" if i == 0 else "#f6eee9"}"/>' for i, (cx, cy) in enumerate(CENTERS))
    return f'<svg viewBox="255 281 658 465" height="{h}" xmlns="http://www.w3.org/2000/svg">{p}</svg>'


def ts(t):
    return time.strftime("%Y-%m-%d %H:%M", time.localtime(t)) if t else "—"


def uname(g, uid):
    m = g.get_member(uid) if g else None
    return E(m.display_name) if m else str(uid)


def fname(fid):
    r = one("SELECT name FROM forums WHERE id=?", (fid,))
    return E(r["name"]) if r else "—"


def badge(t, k):
    return f'<span class="badge b-{k}">{t}</span>'


def st_badge(s):
    t, k = STATUS.get(s, (s, "mut"))
    return badge(t, k)


def btn(act, fid, uid, label, cls="", back="", confirm=""):
    on = f' onsubmit="return confirm(\'{confirm}\')"' if confirm else ""
    return (f'<form method=post action=/fa style="display:inline"{on}>'
            f'<input type=hidden name=act value={act}><input type=hidden name=id value={fid}>'
            f'<input type=hidden name=uid value={uid}><input type=hidden name=back value="{back}">'
            f'<button class="s {cls}">{label}</button></form> ')


def table(head, rows, empty="لا يوجد بيانات"):
    if not rows:
        return f'<div class=empty>{empty}</div>'
    return "<table><thead><tr>" + "".join(f"<th>{h}</th>" for h in head) + "</tr></thead><tbody>" + "".join(rows) + "</tbody></table>"


def shell(body, title="لوحة التحكم"):
    return ('<!doctype html><html dir=rtl lang=ar><head><meta charset=utf-8>'
            '<meta name=viewport content="width=device-width,initial-scale=1">'
            f'<title>{title}</title><link rel=icon href="/icon/forum.png"><style>{CSS}</style></head><body>{body}</body></html>')


def layout(active, title, sub, body, msg=None, g=None):
    pend = one("SELECT COUNT(*) FROM forums WHERE status='pending'")[0]
    nav = ""
    for h, icn, lb in NAV:
        cls = "on" if h == active else ""
        n = f"<span class=n>{pend}</span>" if h == "/requests" and pend else ""
        nav += f'<a href="{h}" class="{cls}">{ic(icn, 20)} {lb}{n}</a>'
    toast = ""
    if msg:
        cls = "err" if msg.startswith("خطأ") else ""
        toast = (f'<div class="toast {cls}" id=t>{ic("cross" if cls else "check", 18)} {E(msg)}</div><script>setTimeout(()=>document.getElementById("t")?.remove(),4500);'
                 'const u=new URL(location);u.searchParams.delete("msg");history.replaceState(null,"",u)</script>')
    gname = E(g.name) if g else ""
    side = (f'<aside class=side><div class=brand>{logo_svg(30)}<span>{gname or "Forums Bot"}</span></div>'
            f'<nav class=nav>{nav}</nav><div class=nav><a class=out href="/logout">{ic("exit", 18)} خروج</a></div></aside>')
    return shell(f'<div class=app>{side}<main><h1>{title}</h1><p class=sub>{sub}</p>{body}</main></div>{toast}', title)


def pg_login(bad=False):
    err = '<p style="color:var(--bad)">كلمة السر غلط</p>' if bad else ""
    return shell('<div class=login><div class=card>' + logo_svg(64) +
                 '<h1 style="margin-top:14px">لوحة التحكم</h1><p class=sub>سجّل دخولك لإدارة البوت</p>' + err +
                 '<form method=post action=/login><input type=password name=p placeholder="كلمة السر" autofocus '
                 'style="width:100%;margin-bottom:12px"><button style="width:100%">دخول</button></form></div></div>')


def accept_form(fid, back):
    o = room_opts()
    num_ = lambda n, lb, v, lo, hi: (f'<div class=fld><label>{lb}</label><input type=number min={lo} max={hi} name={n} value={v}></div>')
    txt = lambda n, lb, v: f'<div class=fld><label>{lb}</label><input name={n} value="{E(v)}" maxlength=30></div>'
    return ('<details><summary><span class="badge b-ok">قبول…</span></summary>'
            '<form method=post action=/fa style="margin-top:8px;min-width:340px;display:grid;grid-template-columns:1fr 1fr;gap:8px">'
            f'<input type=hidden name=act value=accept><input type=hidden name=id value={fid}><input type=hidden name=back value="{back}">'
            + num_("vc", "عدد الرومات الصوتية", o["voice"], 0, 10) + num_("cc", "عدد رومات الشات", o["chat"], 1, 10)
            + txt("vn", "اسم الصوتي (فاضي = اسم المنتدى)", o["vname"]) + txt("cn", "اسم رومات الشات", o["cname"])
            + txt("ow", "اسم روم الأونر", o["oname"]) + '<button style="grid-column:1/-1">قبول وإنشاء</button></form></details>')


def req_rows(g, rows, back):
    out = []
    for f in rows:
        out.append(f"<tr><td>{f['id']}</td><td><b>{E(f['name'])}</b></td><td>{E(f['size'] or '')}</td>"
                   f"<td>{E(f['tiktok'] or '')}</td><td>{uname(g, f['owner_id'])}</td>"
                   f"<td>{accept_form(f['id'], back)}{btn('reject', f['id'], 0, 'رفض', 'd', back)}</td></tr>")
    return out


def pg_overview(g):
    n = lambda sql: one(sql)[0]
    stats = [("forum", "منتديات نشطة", n("SELECT COUNT(*) FROM forums WHERE status='active'")),
             ("inbox", "طلبات معلقة", n("SELECT COUNT(*) FROM forums WHERE status='pending'")),
             ("users", "أعضاء المنتديات", n("SELECT COUNT(*) FROM members WHERE banned=0")),
             ("ban", "محظورون", n("SELECT COUNT(*) FROM members WHERE banned=1")),
             ("clock", "في فترة انتظار", one("SELECT COUNT(*) FROM cooldowns WHERE until>?", (int(time.time()),))[0]),
             ("megaphone", "تجمعات شغالة", n("SELECT COUNT(*) FROM gatherings WHERE active=1"))]
    cards = "".join(f'<div class=stat><span>{ic(i, 18)} {t}</span><b>{v}</b></div>' for i, t, v in stats)
    pend = allrows("SELECT * FROM forums WHERE status='pending' ORDER BY id DESC LIMIT 5")
    logs = [f"<tr><td>{ts(x['ts'])}</td><td>{fname(x['forum_id'])}</td><td>{E(x['text'])}</td></tr>"
            for x in allrows("SELECT * FROM logs ORDER BY id DESC LIMIT 10")]
    return (f'<div class=grid>{cards}</div>'
            f'<div class=card><h2>طلبات تنتظر المراجعة</h2>'
            f'{table(["#", "الاسم", "العدد", "تيك توك", "المقدّم", ""], req_rows(g, pend, "/"), "ما فيه طلبات")}</div>'
            f'<div class=card><h2>آخر النشاطات</h2>{table(["الوقت", "المنتدى", "الحدث"], logs, "لا يوجد نشاط")}</div>')


def pg_requests(g):
    pend = allrows("SELECT * FROM forums WHERE status='pending' ORDER BY id DESC")
    hist = [f"<tr><td>{f['id']}</td><td>{E(f['name'])}</td><td>{E(f['size'] or '')}</td><td>{uname(g, f['owner_id'])}</td>"
            f"<td>{st_badge(f['status'])}</td></tr>"
            for f in allrows("SELECT * FROM forums WHERE status!='pending' ORDER BY id DESC LIMIT 25")]
    return (f'<div class=card><h2>بانتظار القرار</h2>'
            f'{table(["#", "الاسم", "العدد", "تيك توك", "المقدّم", ""], req_rows(g, pend, "/requests"), "ما فيه طلبات")}</div>'
            f'<div class=card><h2>آخر الطلبات المعالجة</h2>{table(["#", "الاسم", "العدد", "المقدّم", "الحالة"], hist, "لا يوجد")}</div>')


def pg_forums(g, qtext="", status=""):
    sql = ("SELECT f.*, (SELECT COUNT(*) FROM members m WHERE m.forum_id=f.id AND m.banned=0) AS mc "
           "FROM forums f WHERE 1=1")
    args = []
    if status in STATUS:
        sql += " AND f.status=?"
        args.append(status)
    if qtext:
        sql += " AND f.name LIKE ?"
        args.append(f"%{qtext}%")
    rows = []
    for f in allrows(sql + " ORDER BY f.id DESC LIMIT 300", tuple(args)):
        rows.append(f"<tr><td>{f['id']}</td><td><a href='/forum?id={f['id']}'><b>{E(f['name'])}</b></a></td>"
                    f"<td>{st_badge(f['status'])}</td><td>{f['mc']}</td><td>{uname(g, f['owner_id'])}</td>"
                    f"<td>{E(f['tiktok'] or '')}</td><td><a class=badge href='/forum?id={f['id']}'>إدارة</a></td></tr>")
    tabs = "".join(f'<a href="/forums?status={k}&q={quote(qtext)}" class="{"on" if status == k else ""}">{lb}</a>'
                   for k, lb in [("", "الكل"), ("active", "نشطة"), ("pending", "معلقة"), ("rejected", "مرفوضة")])
    return (f'<div class=tabs>{tabs}</div><div class=card><form class=row method=get action=/forums>'
            f'<input type=hidden name=status value="{E(status)}"><input name=q value="{E(qtext)}" placeholder="ابحث باسم المنتدى" '
            f'style="flex:1"><button>بحث</button></form></div>'
            f'<div class=card>{table(["#", "الاسم", "الحالة", "الأعضاء", "الأونر", "تيك توك", ""], rows, "لا يوجد منتديات")}</div>')


def pg_forum(g, f):
    fid = f["id"]
    back = f"/forum?id={fid}"
    mem = allrows("SELECT * FROM members WHERE forum_id=? ORDER BY banned, deputy DESC", (fid,))
    cnt = lambda c: sum(1 for m in mem if c(m))
    stats = [("users", "أعضاء", cnt(lambda m: not m["banned"])), ("star", "نواب", cnt(lambda m: m["deputy"])),
             ("ban", "محظورون", cnt(lambda m: m["banned"])),
             ("warn", "تحذيرات", one("SELECT COUNT(*) FROM warnings WHERE forum_id=?", (fid,))[0])]
    cards = "".join(f'<div class=stat><span>{ic(i, 18)} {t}</span><b>{v}</b></div>' for i, t, v in stats)
    rows = []
    for m in mem:
        uid = m["user_id"]
        if uid == f["owner_id"]:
            stt, acts = badge(ic("crown", 14) + " أونر", "warn"), ""
        elif m["banned"]:
            stt, acts = badge("محظور", "bad"), btn("unban", fid, uid, "فك الباند", "g", back)
        else:
            w = one("SELECT COUNT(*) FROM warnings WHERE forum_id=? AND user_id=?", (fid, uid))[0]
            stt = badge(ic("star", 14) + " نائب", "ok") if m["deputy"] else badge("عضو", "mut")
            if w:
                stt += " " + badge(f"{w} تحذير", "warn")
            acts = (btn("dep", fid, uid, "إزالة نائب" if m["deputy"] else "تعيين نائب", "g", back)
                    + btn("owner", fid, uid, "اجعله أونر", "g", back, "نقل الملكية لهذا العضو؟")
                    + (btn("warnclear", fid, uid, "مسح التحذيرات", "g", back) if w else "")
                    + btn("kick", fid, uid, "إخراج", "d", back) + btn("ban", fid, uid, "باند", "d", back))
        rows.append(f"<tr><td>{uname(g, uid)}</td><td>{uid}</td><td>{stt}</td><td>{acts}</td></tr>")
    logs = [f"<tr><td>{ts(x['ts'])}</td><td>{E(x['text'])}</td></tr>"
            for x in allrows("SELECT * FROM logs WHERE forum_id=? ORDER BY id DESC LIMIT 30", (fid,))]
    hid = f"<input type=hidden name=id value={fid}><input type=hidden name=back value='{back}'>"
    return (f'<p><a href="/forums">← كل المنتديات</a></p>'
            f'<div class=card><div class=row><h2 style="margin:0">{E(f["name"])}</h2>{st_badge(f["status"])}'
            f'<span class=hint>الأونر: {uname(g, f["owner_id"])} • تيك توك: {E(f["tiktok"] or "—")}</span></div></div>'
            f'<div class=grid>{cards}</div>'
            f'<div class=card><h2>الأعضاء</h2>{table(["العضو", "ID", "الحالة", ""], rows, "لا يوجد أعضاء")}</div>'
            f'<div class=f2>'
            f'<div class=card><h3>إضافة عضو</h3><form method=post action=/fa class=row>{hid}<input type=hidden name=act value=add>'
            f'<input name=uid placeholder="ID العضو" style="flex:1"><label style="margin:0"><input type=checkbox name=force> تجاوز القيود</label>'
            f'<button>إضافة</button></form></div>'
            f'<div class=card><h3>نشر فعالية</h3><form method=post action=/fa class=row>{hid}<input type=hidden name=act value=event>'
            f'<input name=name placeholder="الفعالية" style="flex:1"><input name=prize placeholder="الجائزة" style="flex:1"><button>نشر</button></form></div>'
            f'<div class=card><h3>تغيير الاسم</h3><form method=post action=/rename class=row><input type=hidden name=id value={fid}>'
            f'<input name=name value="{E(f["name"])}" style="flex:1"><button>حفظ</button></form></div>'
            f'<div class=card><h3>لوحة الأونر</h3><form method=post action=/fa>{hid}<input type=hidden name=act value=panel>'
            f'<button class=g>إعادة نشر اللوحة</button></form> <form method=post action=/fa style="display:inline">{hid}<input type=hidden name=act value=rooms><button class=g>إضافة رومات التجمع والصور</button></form> <form method=post action=/fa style="display:inline">{hid}<input type=hidden name=act value=gpanel><button class=g>إعادة نشر لوحة التجمع</button></form></div></div>'
            f'<div class=card><h2>سجل المنتدى</h2>{table(["الوقت", "الحدث"], logs, "لا يوجد سجل")}</div>'
            f'<div class="card danger"><h3>منطقة الخطر</h3><form method=post action=/delete onsubmit="return confirm(\'حذف المنتدى بكل رومـاته ورتبته؟\')">'
            f'<input type=hidden name=id value={fid}><button class=d>حذف المنتدى نهائياً</button></form></div>')


def pg_gatherings(g):
    rows = [f"<tr><td>{x['id']}</td><td><b>{E(x['server'])}</b></td><td>{E(x['symbol'])}</td><td>{uname(g, x['user_id'])}</td>"
            f"<td>{badge('شغال', 'ok') if x['active'] else badge('منتهي', 'mut')}</td></tr>"
            for x in allrows("SELECT * FROM gatherings ORDER BY id DESC LIMIT 100")]
    return f'<div class=card>{table(["#", "السيرفر", "الرمز", "المسؤول", "الحالة"], rows, "ما فيه تجمعات")}</div>'


def pg_cooldowns(g):
    rows = [f"<tr><td>{uname(g, c['user_id'])}</td><td>{c['user_id']}</td><td>{ts(c['until'])}</td><td>{fname(c['from_forum'])}</td>"
            f"<td>{btn('cdclear', 0, c['user_id'], 'إلغاء الانتظار', 'g', '/cooldowns')}</td></tr>"
            for c in allrows("SELECT * FROM cooldowns WHERE until>? ORDER BY until", (int(time.time()),))]
    return (f'<div class=card>{table(["العضو", "ID", "ينتهي", "من منتدى", ""], rows, "ما فيه أحد في فترة انتظار")}</div>'
            f'<div class=card><h3>إلغاء انتظار عضو بالـ ID</h3><form method=post action=/fa class=row>'
            f'<input type=hidden name=act value=cdclear><input type=hidden name=id value=0><input type=hidden name=back value=/cooldowns>'
            f'<input name=uid placeholder="ID العضو" style="flex:1"><button>إلغاء</button></form></div>')


def pg_logs(g, fid=0):
    sql, a = "SELECT * FROM logs", ()
    if fid:
        sql, a = sql + " WHERE forum_id=?", (fid,)
    rows = [f"<tr><td>{ts(x['ts'])}</td><td>{fname(x['forum_id'])}</td><td>{E(x['text'])}</td></tr>"
            for x in allrows(sql + " ORDER BY id DESC LIMIT 200", a)]
    opts = '<option value="0">كل المنتديات</option>' + "".join(
        f'<option value="{f["id"]}"{" selected" if f["id"] == fid else ""}>{E(f["name"])}</option>'
        for f in allrows("SELECT id,name FROM forums ORDER BY name"))
    return (f'<div class=card><form class=row method=get action=/logs><select name=forum style="flex:1">{opts}</select>'
            f'<button>تصفية</button></form></div><div class=card>{table(["الوقت", "المنتدى", "الحدث"], rows, "لا يوجد سجل")}</div>')


def pg_settings(g):
    def sel(name, options):
        cur = str(get(name) or (DEFAULT_PHOTOS_CH if name == "photos_ch" else ""))
        o = '<option value="">— غير محدد —</option>' + "".join(
            f'<option value="{v}"{" selected" if str(v) == cur else ""}>{E(l)}</option>' for v, l in options)
        return f'<select name="{name}">{o}</select>'

    def sel2(name, options, default):
        cur = str(get(name) if get(name) is not None else default)
        o = "".join(f'<option value="{v}"{" selected" if v == cur else ""}>{E(l)}</option>' for v, l in options)
        return f'<select name="{name}">{o}</select>'

    def fld(label, inner, hint=""):
        return f'<div class=fld><label>{label}</label>{inner}<div class=hint>{hint}</div></div>'

    def numf(name, label, default, hint):
        return fld(label, f'<input type=number min=0 name="{name}" value="{E(str(get(name) if get(name) is not None else default))}">', hint)

    def textf(name, label, default, hint=""):
        return fld(label, f'<input name="{name}" maxlength=30 value="{E(get(name) or default)}">', hint)

    chans = [(c.id, "# " + c.name) for c in g.text_channels]
    roles = [(r.id, r.name) for r in sorted(g.roles, key=lambda r: -r.position) if not r.is_default()]
    return ('<form method=post action=/settings>'
            '<div class=card><h2>الرومات</h2><div class=f2>'
            + fld("روم طلبات المنتديات", sel("requests_ch", chans), "تصل فيه طلبات التقديم")
            + fld("روم إشعارات التجمعات", sel("notices_ch", chans), "تُنشر فيه لوحة التجمعات")
            + fld("روم الصور الرئيسي", sel("photos_ch", chans), "تنتقل له صور كل المنتديات، وينبّه فيه عند انتهاء تجمع") +
            '</div></div><div class=card><h2>الرتب</h2><div class=f2>'
            + fld("رتبة الإدارة", sel("admin_role", roles), "تقبل الطلبات وتتحكم بالبوت")
            + fld("رتبة مسؤول التجمعات", sel("gather_manager_role", roles), "تستخدم لوحة التجمعات")
            + fld("رتبة التجمع", sel("gather_ping_role", roles), "تُمنشن عند إعلان تجمع") +
            '</div></div><div class=card><h2>القواعد والحدود</h2><div class=f2>'
            + numf("min_members", "الحد الأدنى لأعضاء المنتدى", 5, "أقل من كذا يُرفض الطلب تلقائياً")
            + numf("max_forums", "أقصى عدد منتديات للشخص", 1, "يشمل الأونر والعضو والطلبات المعلقة")
            + numf("cooldown_days", "أيام الانتظار بعد الخروج", 3, "0 = بدون انتظار")
            + numf("max_deputies", "أقصى عدد نواب للمنتدى", 2, "")
            + numf("max_warns", "تحذيرات الطرد التلقائي", 3, "0 = بدون طرد تلقائي") +
            '</div></div><div class=card><h2>رومات المنتدى عند القبول</h2><div class=f2>'
            + numf("voice_count", "عدد الرومات الصوتية", 4, "من 0 إلى 10")
            + numf("chat_count", "عدد رومات الشات", 2, "من 1 إلى 10")
            + textf("voice_name", "اسم الرومات الصوتية", "", "فاضي = اسم المنتدى")
            + textf("chat_name", "اسم رومات الشات", "شات")
            + textf("owner_name", "اسم روم الأونر", "اونر") +
            '</div><div class=hint style="margin-top:10px">هذي القيم الافتراضية، وتقدر تعدلها لكل منتدى وقت القبول.</div></div>'
            '<div class=card><h2>نظام إنشاء التجمع (عام)</h2><div class=f2>'
            + fld("روم لوحة التجمع العام", sel("pub_gather_ch", chans), "تُنشر فيه اللوحة وتنزل فيه التجمعات")
            + fld("المنشن", sel2("pub_mention", [("0", "بدون منشن"), ("1", "تفعيل المنشن")], "0"), "")
            + fld("الرتبة اللي تتمنشن", sel("pub_role", roles), "تُستخدم فقط إذا المنشن مفعّل")
            + fld("من يقدر ينشئ تجمع", sel2("pub_everyone", [("0", "مسؤولو التجمعات والإدارة"), ("1", "كل الأعضاء")], "0"), "") +
            '</div></div><button>حفظ الإعدادات</button></form>'
            '<form method=post action=/fa style="margin-top:14px"><input type=hidden name=act value=pubpanel>'
            '<input type=hidden name=id value=0><input type=hidden name=back value=/settings>'
            '<button class=g>نشر لوحة التجمع العام في الروم المحدد</button></form>')


def make_web():
    app = web.Application()

    def guard(r):
        if r.cookies.get("t") != token():
            raise web.HTTPFound("/login")

    def G():
        g = bot.get_guild(GUILD_ID)
        if not g:
            lst = "".join(f"<li>{E(x.name)} — <code>{x.id}</code></li>" for x in bot.guilds) or "<li>البوت مو داخل أي سيرفر، أضفه من رابط الدعوة</li>"
            raise web.HTTPServiceUnavailable(text=shell(
                '<div class=login><div class=card style="text-align:right"><h2>البوت غير متصل بالسيرفر</h2>'
                f'<p>الـ GUILD_ID الحالي: <code>{GUILD_ID}</code></p><p>السيرفرات اللي البوت داخلها:</p><ul>{lst}</ul>'
                '<p class=hint>انسخ ID السيرفر الصحيح وحطه في GUILD_ID بإعدادات Render ثم أعد التشغيل.</p></div></div>'),
                content_type="text/html")
        return g

    def out(s):
        return web.Response(text=s, content_type="text/html")

    def go(path, msg=None):
        sep = "&" if "?" in path else "?"
        raise web.HTTPFound(path + (f"{sep}msg={quote(msg)}" if msg else ""))

    def page(r, active, title, sub, fn, *a):
        guard(r)
        g = G()
        return out(layout(active, title, sub, fn(g, *a), r.query.get("msg"), g))

    async def login_get(r):
        return out(pg_login(r.query.get("e") == "1"))

    async def login(r):
        d = await r.post()
        if hmac.compare_digest(d.get("p", ""), DASH_PASS):
            resp = web.HTTPFound("/")
            resp.set_cookie("t", token(), httponly=True, max_age=86400 * 7, samesite="Lax")
            return resp
        await asyncio.sleep(1)
        go("/login?e=1")

    async def logout(r):
        resp = web.HTTPFound("/login")
        resp.del_cookie("t")
        return resp

    async def overview(r):
        return page(r, "/", "نظرة عامة", "ملخص سريع لكل شيء", pg_overview)

    async def requests_(r):
        return page(r, "/requests", "الطلبات", "اقبل أو ارفض طلبات المنتديات", pg_requests)

    async def forums(r):
        return page(r, "/forums", "المنتديات", "كل المنتديات في السيرفر", pg_forums, r.query.get("q", "").strip(), r.query.get("status", ""))

    async def forum(r):
        guard(r)
        f = one("SELECT * FROM forums WHERE id=?", (int(r.query.get("id", "0") or 0),))
        if not f:
            go("/forums", "خطأ: المنتدى غير موجود")
        g = G()
        return out(layout("/forums", "إدارة المنتدى", "الأعضاء والصلاحيات والفعاليات", pg_forum(g, f), r.query.get("msg"), g))

    async def gatherings(r):
        return page(r, "/gatherings", "التجمعات", "سجل التجمعات", pg_gatherings)

    async def cooldowns(r):
        return page(r, "/cooldowns", "فترات الانتظار", "أعضاء ممنوعين من دخول منتدى جديد مؤقتاً", pg_cooldowns)

    async def logs(r):
        return page(r, "/logs", "السجلات", "آخر 200 حدث", pg_logs, int(r.query.get("forum", "0") or 0))

    async def settings_get(r):
        return page(r, "/settings", "الإعدادات", "الرومات والرتب والحدود", pg_settings)

    async def settings(r):
        guard(r)
        d = await r.post()
        for k in SETTING_KEYS:
            put(k, d.get(k, "").strip())
        go("/settings", "تم حفظ الإعدادات")

    async def rename(r):
        guard(r)
        d = await r.post()
        f = one("SELECT * FROM forums WHERE id=?", (int(d["id"]),))
        new = d["name"].strip()[:40]
        back = f"/forum?id={d['id']}"
        if not f or not new:
            go(back, "خطأ: بيانات ناقصة")
        if name_taken(new, f["id"]):
            go(back, "خطأ: الاسم مستخدم")
        await rename_forum(G(), f, new)
        go(back, "تم تغيير الاسم")

    async def delete(r):
        guard(r)
        d = await r.post()
        f = one("SELECT * FROM forums WHERE id=?", (int(d["id"]),))
        if f:
            await delete_forum(G(), f)
        go("/forums", "تم حذف المنتدى")

    async def fa(r):
        guard(r)
        d = await r.post()
        act, fid = d.get("act"), int(d.get("id") or 0)
        back = d.get("back") or (f"/forum?id={fid}" if fid else "/")
        if not back.startswith("/") or back.startswith("//"):
            back = "/"
        g = G()
        f = one("SELECT * FROM forums WHERE id=?", (fid,))
        uid = int(d["uid"]) if d.get("uid", "").strip().isdigit() else None
        msg = "تم"
        try:
            if act == "pubpanel":
                await send_public_panel(g)
            elif act == "cdclear":
                if not uid:
                    raise ValueError("اكتب ID صحيح")
                q("DELETE FROM cooldowns WHERE user_id=?", (uid,))
            else:
                if not f:
                    raise ValueError("المنتدى غير موجود")
                if act in ("add", "kick", "ban", "unban", "dep", "owner", "warnclear") and uid is None:
                    raise ValueError("اكتب ID صحيح")
                if act in ("accept", "reject"):
                    if f["status"] != "pending":
                        raise ValueError("الطلب تمت معالجته")
                    opts = (room_opts(voice=d.get("vc"), chat=d.get("cc"), vname=d.get("vn"), cname=d.get("cn"),
                                      oname=d.get("ow")) if act == "accept" else None)
                    ok, note = await process_request(g, f, act == "accept", opts)
                    msg = "تم قبول الطلب وإنشاء المنتدى" if ok else "تم رفض الطلب" + (f" ({note})" if note else "")
                elif act == "add":
                    mm = one("SELECT banned FROM members WHERE forum_id=? AND user_id=?", (fid, uid))
                    if not d.get("force"):
                        if mm and mm["banned"]:
                            raise ValueError("العضو محظور من المنتدى")
                        err = check_join(uid, fid)
                        if err:
                            raise ValueError(plain(err))
                    await add_member(g, f, uid)
                elif act in ("kick", "ban"):
                    if uid == f["owner_id"]:
                        raise ValueError("ما تقدر تطرد الأونر")
                    await remove_member(g, f, uid, ban=act == "ban")
                elif act == "unban":
                    await unban_member(g, f, uid)
                elif act == "dep":
                    r0 = one("SELECT deputy FROM members WHERE forum_id=? AND user_id=?", (fid, uid))
                    await set_deputy(g, f, uid, not (r0 and r0["deputy"]))
                elif act == "owner":
                    await transfer_owner(g, f, uid)
                elif act == "warnclear":
                    q("DELETE FROM warnings WHERE forum_id=? AND user_id=?", (fid, uid))
                elif act == "event":
                    await post_event(g, f, d.get("name", "").strip() or "فعالية", d.get("prize", "").strip() or "-")
                elif act == "rooms":
                    made = await ensure_rooms(g, f)
                    msg = ("تم إنشاء: " + "، ".join(made)) if made else "الرومات موجودة"
                elif act == "gpanel":
                    await send_gather_panel(g, f)
                elif act == "panel":
                    await send_panel(g, f)
        except (ValueError, discord.HTTPException) as ex:
            msg = f"خطأ: {ex}"
        go(back, msg)

    async def icon_route(r):
        n = r.match_info["n"]
        if n not in ICONS:
            raise web.HTTPNotFound()
        return web.Response(body=icon_png(n), content_type="image/png", headers={"Cache-Control": "public, max-age=86400"})

    app.add_routes([web.get("/icon/{n}.png", icon_route), web.get("/", overview), web.get("/login", login_get), web.post("/login", login),
                    web.get("/logout", logout), web.get("/requests", requests_), web.get("/forums", forums),
                    web.get("/forum", forum), web.get("/gatherings", gatherings), web.get("/cooldowns", cooldowns),
                    web.get("/logs", logs), web.get("/settings", settings_get), web.post("/settings", settings),
                    web.post("/rename", rename), web.post("/delete", delete), web.post("/fa", fa)])
    return app


_FONT_B64 = (
    "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"
    "BrYpazO5TXWbF9u82+Z0m6/afBcnxnnHhcfp49bF/RCfHJ8dXxjfP35k/Lj4ywkRCVMT5iesSNiQsDNhf8IDY5RxvHGmcZFx"
    "jXGzcafxQaIucWji2MTpiQsSVyVuStyVWJd4MvGzxO8Sf0q8n/goqTRpU9KNpH8lhyabkkuSRyUfTbak9EoZklKRMi2lJmVp"
    "yrlUXeqU1BdSP0v9Z1pkWnxaRlp+WnHa0LSxadPTFqStStuU9klaU1qTSWEKNCWY8k39TVWmd0zvmT5sG9Z2TNt30r3SA9NV"
    "6VHpxvQB6WPSZ6YvSV+XvjV9f/rR9LPpX6ffSL+X/jCDyXDLCMyIymib0TljUMaMjIUZhzJOZJzPuJRxK+Pf7VA793aadrHt"
    "Orbr0W5wu9HtqtrNa7e83avtdrT7od2v7R5lipnemeGZMZlpmfmZxZlDMydkzs1clbkpc1dmXebpzH9m/pR5P7MhS8zyzgrP"
    "islKy8rNKsoalFWeNSVrbtayrNqsXVnvZn2S9c+sH7J+zXrUnm3v0T64vb59Uvsl7T9sb852zvbLVmfHZadnd8rulT0kuyJ7"
    "WnZN9srsjdlvZh/KPpF9PvtS9q3s37Of5gg5ypywnOic1JwOOb1yhudMzqnJeTlnW87bOe/nfAwrUzmu5cuFnbAyKRjGR6lW"
    "6tRKdTnPNFVxIU13cK3C48mfU8RohkURsJAtFi7BiuUMFpBayak5qK5GEWhMMsbJaAzeIFwyn8FD0XbzF3gz4D7D7eXGwBMU"
    "N1Jq6A835vfPf4eKl9hYUsjquJxhxGjhJBPCQBuIU/skc2o/NS0aH1pS1bQgAHKrS5HT8O+HIz/8bicUig+Wfl+Kn5TeLMW/"
    "oM75+A4qLkU98ZN85CScxPNQDZ53Cd+/jGvQPFIuI+9LqMa8F98Hqrbii4Io+jIaJoZJhJY1nF5vUPr7BygNen1qSprJlOwH"
    "V34EGuDv7+crKjilKPr5+vso09JSU/RcyHZU/evEqt9mqf84/9dttH3UuTL4r8JfPny8vaBv0YP+/XviiyhOiI9GYrtsHpnE"
    "mCNvHT7vfPe2U2QIjkkQ8C0x6oP3jn7sweUige+U2q4jPoR/Rbm5eR3BxGNyLbcVZ4QHjCsTANwxMMlAZSQhIDmJtG9IIkRp"
    "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"
)


if __name__ == "__main__":
    if "assets" in sys.argv:
        make_assets()
        sys.exit(0)
    if not TOKEN or not GUILD_ID:
        sys.exit("ضع DISCORD_TOKEN و GUILD_ID في ملف .env")
    try:
        bot.run(TOKEN)
    except discord.PrivilegedIntentsRequired:
        sys.exit("فعّل Server Members Intent و Message Content Intent من بوابة المطورين (Bot ← Privileged Gateway Intents)")
