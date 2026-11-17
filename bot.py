import os, io, re, sys, hmac, hashlib, time, sqlite3, html, asyncio
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
COLOR = 0x967A62

# ───────────── الصور (لوقو + لوحات) ─────────────
W, H = 1170, 1130
BG = (150, 122, 96)
CENTERS = [(585, 389), (475, 513), (695, 513), (363, 638), (585, 638), (805, 638)]
R = 108
FONT_PATH = os.path.join(os.path.dirname(__file__), "assets", "font.ttf")


def _fix(t):
    try:
        import arabic_reshaper
        from bidi.algorithm import get_display
        return get_display(arabic_reshaper.reshape(t))
    except Exception:
        return t


def logo(name=None) -> bytes:
    S = 2
    img = Image.new("RGB", (W * S, H * S), BG)
    sh = Image.new("L", img.size, 0)
    d = ImageDraw.Draw(sh)
    for cx, cy in CENTERS:
        o = 16
        d.polygon([(cx * S, (cy - R + o) * S), ((cx + R) * S, (cy + o) * S),
                   (cx * S, (cy + R + o) * S), ((cx - R) * S, (cy + o) * S)], fill=160)
    sh = sh.filter(ImageFilter.GaussianBlur(18 * S))
    img.paste(Image.new("RGB", img.size, (70, 52, 36)), mask=sh)
    for i, (cx, cy) in enumerate(CENTERS):
        top, bot = ((205, 190, 180), (190, 175, 166)) if i == 0 else ((243, 235, 230), (252, 246, 242))
        n = 2 * R * S
        tile = Image.new("RGB", (n, n))
        td = ImageDraw.Draw(tile)
        for y in range(n):
            t = y / n
            td.line([(0, y), (n, y)], fill=tuple(int(top[k] + (bot[k] - top[k]) * t) for k in range(3)))
        m = Image.new("L", (n, n), 0)
        ImageDraw.Draw(m).polygon([(n // 2, 0), (n, n // 2), (n // 2, n), (0, n // 2)], fill=255)
        img.paste(tile, ((cx - R) * S, (cy - R) * S), m)
    img = img.resize((W, H), Image.LANCZOS)
    if name:
        try:
            f = ImageFont.truetype(FONT_PATH, 90)
        except Exception:
            try:
                f = ImageFont.load_default(size=90)
            except Exception:
                f = ImageFont.load_default()
        d = ImageDraw.Draw(img)
        d.text((W // 2, 930), _fix(name), font=f, fill=(250, 244, 240), anchor="mm")
    b = io.BytesIO()
    img.save(b, "PNG")
    return b.getvalue()




# ───────── صور المشروع (GitHub / أفتار) ─────────
def mark(height, pad=0):
    """علامة البلاطات بشفافية وظل، بارتفاع محدد"""
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
        tile = Image.new("RGB", (n, n))
        td = ImageDraw.Draw(tile)
        for y in range(n):
            t = y / n
            td.line([(0, y), (n, y)], fill=tuple(int(top[k] + (bot[k] - top[k]) * t) for k in range(3)))
        m = Image.new("L", (n, n), 0)
        ImageDraw.Draw(m).polygon([(n // 2, 0), (n, n // 2), (n // 2, n), (0, n // 2)], fill=255)
        full.paste(tile, ((cx - R) * S, (cy - R) * S), m)
    full = full.crop((200 * S, 230 * S, 950 * S, 830 * S))
    r = height / full.height
    return full.resize((int(full.width * r), height), Image.LANCZOS)


def _bg(w, h):
    base = Image.new("RGB", (w, h), BG)
    px = base.load()
    for x in range(w):
        t = x / w
        c = tuple(int(a + (b - a) * t) for a, b in zip((166, 137, 108), (128, 102, 78)))
        for y in range(h):
            px[x, y] = c
    return base


def _font(path, size):
    try:
        return ImageFont.truetype(path, size)
    except Exception:
        return ImageFont.load_default(size=size)


def _paste(base, layer, xy):
    rgba = base.convert("RGBA")
    rgba.alpha_composite(layer, xy)
    return rgba.convert("RGB")


def _png(im):
    b = io.BytesIO()
    im.save(b, "PNG")
    return b.getvalue()


def avatar(size=512):
    im = Image.new("RGB", (size, size), BG)
    mk = mark(int(size * 0.60))
    im = _paste(im, mk, ((size - mk.width) // 2, (size - mk.height) // 2 + int(size * 0.03)))
    return _png(im)


def banner(title, sub, tags, font, w=1600, h=500):
    im = _bg(w, h)
    mk = mark(int(h * 0.74))
    im = _paste(im, mk, (int(w * 0.07), (h - mk.height) // 2))
    d = ImageDraw.Draw(im)
    x = int(w * 0.07) + mk.width + int(w * 0.05)
    d.text((x, int(h * 0.20)), title, font=_font(font, int(h * 0.26)), fill=(252, 246, 242))
    d.text((x + 4, int(h * 0.55)), sub, font=_font(font, int(h * 0.075)), fill=(235, 222, 212))
    d.text((x + 4, int(h * 0.70)), tags, font=_font(font, int(h * 0.055)), fill=(214, 196, 182))
    return _png(im)


def social(title, sub, font, w=1280, h=640):
    im = _bg(w, h)
    mk = mark(int(h * 0.50))
    im = _paste(im, mk, ((w - mk.width) // 2, int(h * 0.07)))
    d = ImageDraw.Draw(im)
    d.text((w // 2, int(h * 0.74)), title, font=_font(font, int(h * 0.13)), fill=(252, 246, 242), anchor="mm")
    d.text((w // 2, int(h * 0.88)), sub, font=_font(font, int(h * 0.045)), fill=(235, 222, 212), anchor="mm")
    return _png(im)


def panel_example(name, font):
    global FONT_PATH
    old, FONT_PATH = FONT_PATH, font
    try:
        return logo(name)
    finally:
        FONT_PATH = old


def make_assets():
    font = os.environ.get("ASSET_FONT", "/usr/share/fonts/opentype/inter/Inter-Bold.otf")
    name = os.environ.get("BOT_NAME", "Forums Bot")
    sub, tags = "Discord forum & gathering manager", "Requests  •  Roles & channels  •  Gatherings  •  Dashboard"
    os.makedirs("images", exist_ok=True)
    files = {"logo.png": logo(), "avatar.png": avatar(), "banner.png": banner(name, sub, tags, font),
             "social-preview.png": social(name, sub, font), "panel-example.png": panel_example("Falcons Forum", font)}
    for n, data in files.items():
        open(os.path.join("images", n), "wb").write(data)
        print("OK images/" + n)



# ───────────── قاعدة البيانات ─────────────
con = sqlite3.connect("data.db", check_same_thread=False)
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
try:
    con.execute("ALTER TABLE members ADD COLUMN deputy INTEGER DEFAULT 0")
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
    "photos_ch": "روم صور التجمعات (ID)",
    "gather_ping_role": "رتبة التجمع - تنمنشن (ID)",
    "gather_manager_role": "رتبة مسؤول التجمعات (ID)",
    "admin_role": "رتبة الإدارة (ID)",
    "min_members": "الحد الأدنى لأعضاء المنتدى (رقم، الافتراضي 5)",
    "max_forums": "أقصى عدد منتديات للشخص الواحد (الافتراضي 1)",
    "cooldown_days": "أيام الانتظار بعد الخروج من منتدى (الافتراضي 3، و0 = بدون)",
    "max_deputies": "أقصى عدد نواب للمنتدى (الافتراضي 2)",
    "max_warns": "عدد التحذيرات اللي يطلّع العضو تلقائياً (الافتراضي 3، و0 = بدون)",
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
PANEL_BUTTONS = [("invite", "➕ دعوة"), ("kick", "🚪 إخراج"), ("ban", "🚫 باند"), ("unban", "♻️ فك باند"),
                 ("warn", "⚠️ تحذير"), ("event", "🎉 فعالية"), ("log", "📜 اللوق"),
                 ("deputy", "⭐ نائب"), ("rename", "✏️ الاسم")]
OWNER_ONLY = {"rename", "deputy"}


async def create_forum(guild, f):
    name = f["name"]
    owner = guild.get_member(f["owner_id"]) or await guild.fetch_member(f["owner_id"])
    role = await guild.create_role(name=name, reason="forum approved")
    cat = await guild.create_category(name, overwrites={
        guild.default_role: P(view_channel=False),
        role: P(view_channel=True, connect=True, speak=True, send_messages=True, read_message_history=True),
        guild.me: P(view_channel=True, send_messages=True, manage_channels=True)})
    for n in range(1, 5):
        await guild.create_voice_channel(f"🔊 صوتي {n}", category=cat)
    chat = None
    for n in range(1, 4):
        c = await guild.create_text_channel(f"💬 شات {n}", category=cat)
        chat = chat or c
    panel = await guild.create_text_channel(f"👑 اونر {name}"[:100], category=cat, overwrites={
        guild.default_role: P(view_channel=False), role: P(view_channel=False),
        owner: P(view_channel=True, read_message_history=True),
        guild.me: P(view_channel=True, send_messages=True, attach_files=True)})
    await owner.add_roles(role)
    q("UPDATE forums SET status='active',role_id=?,category_id=?,panel_id=?,chat_id=? WHERE id=?",
      (role.id, cat.id, panel.id, chat.id, f["id"]))
    q("INSERT OR REPLACE INTO members(forum_id,user_id,banned) VALUES(?,?,0)", (f["id"], owner.id))
    await send_panel(guild, one("SELECT * FROM forums WHERE id=?", (f["id"],)))
    add_log(f["id"], "تم إنشاء المنتدى بواسطة الإدارة")


async def send_panel(guild, f):
    pn = guild.get_channel(f["panel_id"] or 0)
    if not pn:
        raise ValueError("روم اللوحة غير موجود")
    v = discord.ui.View(timeout=None)
    for a, _ in PANEL_BUTTONS:
        v.add_item(PanelBtn(a, f["id"]))
    e = discord.Embed(title=f"لوحة تحكم {f['name']}", description="تحكم بمنتداك من الأزرار تحت.", color=COLOR)
    e.set_image(url="attachment://panel.png")
    await pn.send(f"<@{f['owner_id']}>", embed=e, view=v,
                  file=discord.File(io.BytesIO(logo(f["name"])), "panel.png"))


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
    if pn:
        await pn.edit(name=f"👑 اونر {new}"[:100])
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
        await ch.send(f"👋 {m.mention} انضم للمنتدى")
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
        txt = f"{'تم حظرك' if ban else 'تم إخراجك'} من منتدى **{f['name']}**."
        if days > 0:
            txt += f"\nتقدر تدخل منتدى ثاني بعد <t:{until}:R>."
        await u.send(txt)
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
    e = discord.Embed(title="🎉 فعالية جديدة", color=COLOR)
    e.add_field(name="الفعالية", value=name)
    e.add_field(name="الجائزة", value=prize)
    await ch.send(role.mention if role else None, embed=e, allowed_mentions=discord.AllowedMentions(roles=True))
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
            return await i.response.send_message("❌ اسم المنتدى مستخدم، اختر اسم ثاني.", ephemeral=True)
        err = check_join(i.user.id)
        if err:
            return await i.response.send_message("❌ " + err, ephemeral=True)
        count, minimum = int(raw), int(get("min_members") or 5)
        if count < minimum:
            q("INSERT INTO forums(name,owner_id,tiktok,size,status) VALUES(?,?,?,?,'rejected')",
              (name, i.user.id, str(self.tiktok), raw))
            e = discord.Embed(title="طلب مرفوض تلقائياً", color=0xB33A3A,
                              description=f"{i.user.mention} قدّم **{name}** بعدد {count} (الحد الأدنى {minimum})")
            await ch.send(embed=e)
            return await i.response.send_message(
                f"❌ تم رفض الطلب: لازم يكون عدد أعضاء المنتدى {minimum} على الأقل (عدد منتداك {count}).",
                ephemeral=True)
        fid = q("INSERT INTO forums(name,owner_id,tiktok,size,status) VALUES(?,?,?,?,'pending')",
                (name, i.user.id, str(self.tiktok), raw)).lastrowid
        e = discord.Embed(title="طلب منتدى جديد", color=COLOR)
        e.add_field(name="الاسم", value=name)
        e.add_field(name="العدد", value=raw)
        e.add_field(name="التيك توك", value=str(self.tiktok))
        e.add_field(name="المقدّم", value=i.user.mention, inline=False)
        v = discord.ui.View(timeout=None)
        v.add_item(RqBtn("ok", fid))
        v.add_item(RqBtn("no", fid))
        await ch.send(embed=e, view=v)
        await i.response.send_message("تم إرسال طلبك للإدارة ✅", ephemeral=True)


class ApplyView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="تقديم منتدى", style=discord.ButtonStyle.primary, custom_id="apply")
    async def b(self, i, _):
        await i.response.send_modal(ApplyModal())


async def process_request(guild, f, accept):
    note = ""
    if accept:
        err = check_join(f["owner_id"], None, skip_pending=f["id"])
        if err or name_taken(f["name"], f["id"]):
            accept, note = False, plain(err or "اسم المنتدى مستخدم")
    if accept:
        await create_forum(guild, f)
    else:
        q("UPDATE forums SET status='rejected' WHERE id=?", (f["id"],))
    try:
        u = await bot.fetch_user(f["owner_id"])
        await u.send(f"طلب منتدى **{f['name']}** تم {'قبوله ✅' if accept else 'رفضه ❌'}" + (f"\n{note}" if note else ""))
    except discord.HTTPException:
        pass
    return accept, note


class RqBtn(discord.ui.DynamicItem[discord.ui.Button], template=r"rq:(?P<a>ok|no):(?P<f>\d+)"):
    def __init__(self, a, f):
        ok = a == "ok"
        super().__init__(discord.ui.Button(label="قبول" if ok else "رفض",
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
        await i.response.defer()
        ok, note = await process_request(i.guild, f, self.a == "ok")
        e = i.message.embeds[0]
        e.color = 0x3A9B5C if ok else 0xB33A3A
        e.set_footer(text=f"مقبول بواسطة {i.user}" if ok else f"مرفوض بواسطة {i.user}" + (f" (تلقائي: {note})" if note else ""))
        await i.message.edit(embed=e, view=None)


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
            return await i.response.send_message("❌ الاسم مستخدم.", ephemeral=True)
        await i.response.defer(ephemeral=True)
        await rename_forum(i.guild, self.f, new)
        await i.followup.send("تم تغيير الاسم ✅", ephemeral=True)


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
            return await i.response.send_message(f"❌ {ex}", ephemeral=True)
        await i.response.send_message("تم نشر الفعالية ✅", ephemeral=True)


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
            await u.send(f"⚠️ وصلك تحذير ({n}/{mx or '∞'}) من منتدى **{f['name']}**\nالسبب: {self.r}")
        except discord.HTTPException:
            pass
        if mx and n >= mx:
            q("DELETE FROM warnings WHERE forum_id=? AND user_id=?", (f["id"], u.id))
            await remove_member(i.guild, f, u.id)
            add_log(f["id"], f"إخراج تلقائي بعد {n} تحذيرات ({u.id})")
            msg = f"وصل {u.mention} إلى {n} تحذيرات وتم إخراجه تلقائياً ✅"
        else:
            msg = f"تم تحذير {u.mention} ({n}/{mx or '∞'}) ✅"
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
        return await i.response.edit_message(content="❌ " + err, view=None)
    v = discord.ui.View(timeout=None)
    v.add_item(IvBtn("ok", f["id"]))
    v.add_item(IvBtn("no", f["id"]))
    try:
        await user.send(f"📩 منتدى **{f['name']}** أرسل لك دعوة دخول.", view=v)
    except discord.HTTPException:
        return await i.response.edit_message(content="ما قدرت أرسل له خاص (الخاص مقفل).", view=None)
    add_log(f["id"], f"دعوة أُرسلت إلى {user} ({user.id})")
    await i.response.edit_message(content="تم إرسال الدعوة ✅", view=None)


async def _remove(i, f, user, ban):
    err = protect(f, i.user, user.id)
    if err:
        return await i.response.edit_message(content=err, view=None)
    m = one("SELECT * FROM members WHERE forum_id=? AND user_id=?", (f["id"], user.id))
    if not ban and not m:
        return await i.response.edit_message(content="العضو مو بالمنتدى.", view=None)
    await i.response.defer()
    await remove_member(i.guild, f, user.id, ban=ban)
    await i.edit_original_response(content=f"تم {'حظر' if ban else 'إخراج'} {user.mention} ✅", view=None)


async def kick_cb(i, f, user):
    await _remove(i, f, user, False)


async def ban_cb(i, f, user):
    await _remove(i, f, user, True)


async def unban_cb(i, f, user):
    await i.response.defer()
    try:
        await unban_member(i.guild, f, user.id)
        msg = f"تم فك الباند عن {user.mention} ✅"
    except ValueError as ex:
        msg = f"❌ {ex}"
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
        msg = f"{'تم تعيين' if on else 'تمت إزالة'} {user.mention} {'نائب' if on else 'من النواب'} ✅"
    except ValueError as ex:
        msg = f"❌ {ex}"
    await i.edit_original_response(content=msg, view=None)


class PanelBtn(discord.ui.DynamicItem[discord.ui.Button], template=r"fp:(?P<a>\w+):(?P<f>\d+)"):
    def __init__(self, a, f):
        super().__init__(discord.ui.Button(label=dict(PANEL_BUTTONS).get(a, a), style=discord.ButtonStyle.secondary,
                                           custom_id=f"fp:{a}:{f}"))
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
        super().__init__(discord.ui.Button(label="قبول" if ok else "رفض",
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
            return await i.response.edit_message(content="❌ " + err, view=None)
        await i.response.defer()
        try:
            await add_member(g, f, i.user.id)
        except ValueError as ex:
            return await i.edit_original_response(content=f"❌ {ex}", view=None)
        await i.edit_original_response(content=f"تم دخولك منتدى **{f['name']}** ✅", view=None)


# ───────────── التجمعات ─────────────
def can_gather(m):
    return is_admin(m) or has_role(m, "gather_manager_role")


class GatherModal(discord.ui.Modal, title="تجمع جديد"):
    server = discord.ui.TextInput(label="اسم السيرفر", max_length=60)
    symbol = discord.ui.TextInput(label="رمز السيرفر", max_length=20)

    async def on_submit(self, i):
        role = i.guild.get_role(int(get("gather_ping_role") or 0))
        e = discord.Embed(title="📢 تجمع جديد", color=0x3A9B5C)
        e.add_field(name="السيرفر", value=str(self.server))
        e.add_field(name="الرمز", value=str(self.symbol))
        e.add_field(name="المسؤول", value=i.user.mention, inline=False)
        msg = await i.channel.send(role.mention if role else None, embed=e,
                                   allowed_mentions=discord.AllowedMentions(roles=True))
        q("INSERT INTO gatherings(user_id,server,symbol,channel_id,message_id) VALUES(?,?,?,?,?)",
          (i.user.id, str(self.server), str(self.symbol), i.channel.id, msg.id))
        await i.response.send_message("تم إعلان التجمع ✅", ephemeral=True)


class GatherView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="تجمع", style=discord.ButtonStyle.success, custom_id="g:start")
    async def start(self, i, _):
        if not can_gather(i.user):
            return await i.response.send_message("لمسؤول التجمعات فقط.", ephemeral=True)
        await i.response.send_modal(GatherModal())

    @discord.ui.button(label="انتهى تجمع", style=discord.ButtonStyle.danger, custom_id="g:end")
    async def end(self, i, _):
        if not can_gather(i.user):
            return await i.response.send_message("لمسؤول التجمعات فقط.", ephemeral=True)
        rows = allrows("SELECT * FROM gatherings WHERE user_id=? AND active=1", (i.user.id,))
        if not rows:
            return await i.response.send_message("ما عندك تجمع شغال.", ephemeral=True)
        await i.response.defer(ephemeral=True)
        for g in rows:
            q("UPDATE gatherings SET active=0 WHERE id=?", (g["id"],))
            try:
                m = await i.channel.fetch_message(g["message_id"])
                e = m.embeds[0]
                e.title, e.color = "🔴 انتهى التجمع", 0xB33A3A
                await m.edit(content=None, embed=e)
            except discord.HTTPException:
                pass
            ph = i.guild.get_channel(int(get("photos_ch") or 0))
            if ph:
                await ph.send(f"📸 انتهى تجمع **{g['server']}** ({g['symbol']}) — شاركوا صور التجمع هنا.")
        await i.followup.send("تم إنهاء التجمع ✅", ephemeral=True)


# ───────────── البوت والأوامر ─────────────
class Bot(commands.Bot):
    def __init__(self):
        it = discord.Intents.default()
        it.members = True
        super().__init__(command_prefix="!", intents=it)

    async def setup_hook(self):
        self.add_dynamic_items(RqBtn, PanelBtn, IvBtn)
        self.add_view(ApplyView())
        self.add_view(GatherView())
        g = discord.Object(GUILD_ID)
        self.tree.copy_global_to(guild=g)
        await self.tree.sync(guild=g)
        runner = web.AppRunner(make_web())
        await runner.setup()
        await web.TCPSite(runner, "0.0.0.0", PORT).start()

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
                        title="⚠️ أونر منتدى طلع من السيرفر", color=0xB33A3A,
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
    await i.response.send_message("تم الحفظ ✅", ephemeral=True)


@bot.tree.command(name="apply_panel", description="نشر زر تقديم المنتدى هنا")
async def apply_panel(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    e = discord.Embed(title="تقديم منتدى", description="اضغط الزر وعبّي البيانات.", color=COLOR)
    e.set_image(url="attachment://logo.png")
    await i.channel.send(embed=e, view=ApplyView(), file=discord.File(io.BytesIO(logo()), "logo.png"))
    await i.response.send_message("تم ✅", ephemeral=True)


@bot.tree.command(name="notice_panel", description="نشر لوحة التجمعات في روم الإشعارات")
async def notice_panel(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    ch = i.guild.get_channel(int(get("notices_ch") or 0)) or i.channel
    await ch.send(embed=discord.Embed(title="لوحة التجمعات", description="ابدأ تجمع أو أنهِ تجمعك.", color=COLOR),
                  view=GatherView())
    await i.response.send_message("تم ✅", ephemeral=True)


@bot.tree.command(name="backup", description="نسخة احتياطية من إعدادات وبيانات البوت")
async def backup(i: discord.Interaction):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    d = sqlite3.connect("backup.db")
    con.backup(d)
    d.close()
    await i.response.send_message("نسختك:", file=discord.File("backup.db", f"backup-{int(time.time())}.db"),
                                  ephemeral=True)


@bot.tree.command(name="restore", description="استرجاع نسخة احتياطية")
async def restore(i: discord.Interaction, file: discord.Attachment):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    await file.save("restore.db")
    try:
        s = sqlite3.connect("restore.db")
        s.execute("SELECT 1 FROM forums LIMIT 1")
        s.backup(con)
        s.close()
    except Exception as ex:
        return await i.response.send_message(f"ملف غير صالح: {ex}", ephemeral=True)
    await i.response.send_message("تم الاسترجاع ✅", ephemeral=True)


@bot.tree.command(name="set_font", description="رفع خط (ttf/otf) للصور")
async def set_font(i: discord.Interaction, file: discord.Attachment):
    if not admin_only(i):
        return await i.response.send_message("للإدارة فقط.", ephemeral=True)
    os.makedirs(os.path.dirname(FONT_PATH), exist_ok=True)
    await file.save(FONT_PATH)
    await i.response.send_message("تم تغيير الخط ✅", ephemeral=True)


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
NAV = [("/", "📊", "نظرة عامة"), ("/requests", "📥", "الطلبات"), ("/forums", "🏛️", "المنتديات"),
       ("/gatherings", "📢", "التجمعات"), ("/cooldowns", "⏳", "الانتظار"), ("/logs", "📜", "السجلات"),
       ("/settings", "⚙️", "الإعدادات")]


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
            f'<title>{title}</title><style>{CSS}</style></head><body>{body}</body></html>')


def layout(active, title, sub, body, msg=None, g=None):
    pend = one("SELECT COUNT(*) FROM forums WHERE status='pending'")[0]
    nav = ""
    for h, ic, lb in NAV:
        cls = "on" if h == active else ""
        n = f"<span class=n>{pend}</span>" if h == "/requests" and pend else ""
        nav += f'<a href="{h}" class="{cls}">{ic} {lb}{n}</a>'
    toast = ""
    if msg:
        cls = "err" if msg.startswith("❌") else ""
        toast = (f'<div class="toast {cls}" id=t>{E(msg)}</div><script>setTimeout(()=>document.getElementById("t")?.remove(),4500);'
                 'const u=new URL(location);u.searchParams.delete("msg");history.replaceState(null,"",u)</script>')
    gname = E(g.name) if g else ""
    side = (f'<aside class=side><div class=brand>{logo_svg(30)}<span>{gname or "Forums Bot"}</span></div>'
            f'<nav class=nav>{nav}</nav><div class=nav><a class=out href="/logout">🚪 خروج</a></div></aside>')
    return shell(f'<div class=app>{side}<main><h1>{title}</h1><p class=sub>{sub}</p>{body}</main></div>{toast}', title)


def pg_login(bad=False):
    err = '<p style="color:var(--bad)">كلمة السر غلط</p>' if bad else ""
    return shell('<div class=login><div class=card>' + logo_svg(64) +
                 '<h1 style="margin-top:14px">لوحة التحكم</h1><p class=sub>سجّل دخولك لإدارة البوت</p>' + err +
                 '<form method=post action=/login><input type=password name=p placeholder="كلمة السر" autofocus '
                 'style="width:100%;margin-bottom:12px"><button style="width:100%">دخول</button></form></div></div>')


def req_rows(g, rows, back):
    out = []
    for f in rows:
        out.append(f"<tr><td>{f['id']}</td><td><b>{E(f['name'])}</b></td><td>{E(f['size'] or '')}</td>"
                   f"<td>{E(f['tiktok'] or '')}</td><td>{uname(g, f['owner_id'])}</td>"
                   f"<td>{btn('accept', f['id'], 0, 'قبول', '', back)}{btn('reject', f['id'], 0, 'رفض', 'd', back)}</td></tr>")
    return out


def pg_overview(g):
    n = lambda sql: one(sql)[0]
    stats = [("🏛️", "منتديات نشطة", n("SELECT COUNT(*) FROM forums WHERE status='active'")),
             ("📥", "طلبات معلقة", n("SELECT COUNT(*) FROM forums WHERE status='pending'")),
             ("👥", "أعضاء المنتديات", n("SELECT COUNT(*) FROM members WHERE banned=0")),
             ("🚫", "محظورون", n("SELECT COUNT(*) FROM members WHERE banned=1")),
             ("⏳", "في فترة انتظار", one("SELECT COUNT(*) FROM cooldowns WHERE until>?", (int(time.time()),))[0]),
             ("📢", "تجمعات شغالة", n("SELECT COUNT(*) FROM gatherings WHERE active=1"))]
    cards = "".join(f'<div class=stat><span>{i} {t}</span><b>{v}</b></div>' for i, t, v in stats)
    pend = allrows("SELECT * FROM forums WHERE status='pending' ORDER BY id DESC LIMIT 5")
    logs = [f"<tr><td>{ts(x['ts'])}</td><td>{fname(x['forum_id'])}</td><td>{E(x['text'])}</td></tr>"
            for x in allrows("SELECT * FROM logs ORDER BY id DESC LIMIT 10")]
    return (f'<div class=grid>{cards}</div>'
            f'<div class=card><h2>طلبات تنتظر المراجعة</h2>'
            f'{table(["#", "الاسم", "العدد", "تيك توك", "المقدّم", ""], req_rows(g, pend, "/"), "ما فيه طلبات ✨")}</div>'
            f'<div class=card><h2>آخر النشاطات</h2>{table(["الوقت", "المنتدى", "الحدث"], logs, "لا يوجد نشاط")}</div>')


def pg_requests(g):
    pend = allrows("SELECT * FROM forums WHERE status='pending' ORDER BY id DESC")
    hist = [f"<tr><td>{f['id']}</td><td>{E(f['name'])}</td><td>{E(f['size'] or '')}</td><td>{uname(g, f['owner_id'])}</td>"
            f"<td>{st_badge(f['status'])}</td></tr>"
            for f in allrows("SELECT * FROM forums WHERE status!='pending' ORDER BY id DESC LIMIT 25")]
    return (f'<div class=card><h2>بانتظار القرار</h2>'
            f'{table(["#", "الاسم", "العدد", "تيك توك", "المقدّم", ""], req_rows(g, pend, "/requests"), "ما فيه طلبات ✨")}</div>'
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
    stats = [("👥", "أعضاء", cnt(lambda m: not m["banned"])), ("⭐", "نواب", cnt(lambda m: m["deputy"])),
             ("🚫", "محظورون", cnt(lambda m: m["banned"])),
             ("⚠️", "تحذيرات", one("SELECT COUNT(*) FROM warnings WHERE forum_id=?", (fid,))[0])]
    cards = "".join(f'<div class=stat><span>{i} {t}</span><b>{v}</b></div>' for i, t, v in stats)
    rows = []
    for m in mem:
        uid = m["user_id"]
        if uid == f["owner_id"]:
            stt, acts = badge("👑 أونر", "warn"), ""
        elif m["banned"]:
            stt, acts = badge("محظور", "bad"), btn("unban", fid, uid, "فك الباند", "g", back)
        else:
            w = one("SELECT COUNT(*) FROM warnings WHERE forum_id=? AND user_id=?", (fid, uid))[0]
            stt = badge("⭐ نائب", "ok") if m["deputy"] else badge("عضو", "mut")
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
            f'<button class=g>إعادة نشر اللوحة</button></form></div></div>'
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
        cur = str(get(name) or "")
        o = '<option value="">— غير محدد —</option>' + "".join(
            f'<option value="{v}"{" selected" if str(v) == cur else ""}>{E(l)}</option>' for v, l in options)
        return f'<select name="{name}">{o}</select>'

    def fld(label, inner, hint=""):
        return f'<div class=fld><label>{label}</label>{inner}<div class=hint>{hint}</div></div>'

    def numf(name, label, default, hint):
        return fld(label, f'<input type=number min=0 name="{name}" value="{E(str(get(name) if get(name) is not None else default))}">', hint)

    chans = [(c.id, "# " + c.name) for c in g.text_channels]
    roles = [(r.id, r.name) for r in sorted(g.roles, key=lambda r: -r.position) if not r.is_default()]
    return ('<form method=post action=/settings>'
            '<div class=card><h2>الرومات</h2><div class=f2>'
            + fld("روم طلبات المنتديات", sel("requests_ch", chans), "تصل فيه طلبات التقديم")
            + fld("روم إشعارات التجمعات", sel("notices_ch", chans), "تُنشر فيه لوحة التجمعات")
            + fld("روم صور التجمعات", sel("photos_ch", chans), "ينبّه فيه البوت عند انتهاء تجمع") +
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
            '</div></div><button>حفظ الإعدادات</button></form>')


def make_web():
    app = web.Application()

    def guard(r):
        if r.cookies.get("t") != token():
            raise web.HTTPFound("/login")

    def G():
        g = bot.get_guild(GUILD_ID)
        if not g:
            raise web.HTTPServiceUnavailable(text="البوت غير متصل بالسيرفر")
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
            go("/forums", "❌ المنتدى غير موجود")
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
        go("/settings", "تم حفظ الإعدادات ✅")

    async def rename(r):
        guard(r)
        d = await r.post()
        f = one("SELECT * FROM forums WHERE id=?", (int(d["id"]),))
        new = d["name"].strip()[:40]
        back = f"/forum?id={d['id']}"
        if not f or not new:
            go(back, "❌ بيانات ناقصة")
        if name_taken(new, f["id"]):
            go(back, "❌ الاسم مستخدم")
        await rename_forum(G(), f, new)
        go(back, "تم تغيير الاسم ✅")

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
        msg = "تم ✅"
        try:
            if act == "cdclear":
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
                    ok, note = await process_request(g, f, act == "accept")
                    msg = "تم قبول الطلب وإنشاء المنتدى ✅" if ok else "تم رفض الطلب" + (f" ({note})" if note else "")
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
                elif act == "panel":
                    await send_panel(g, f)
        except (ValueError, discord.HTTPException) as ex:
            msg = f"❌ {ex}"
        go(back, msg)

    app.add_routes([web.get("/", overview), web.get("/login", login_get), web.post("/login", login),
                    web.get("/logout", logout), web.get("/requests", requests_), web.get("/forums", forums),
                    web.get("/forum", forum), web.get("/gatherings", gatherings), web.get("/cooldowns", cooldowns),
                    web.get("/logs", logs), web.get("/settings", settings_get), web.post("/settings", settings),
                    web.post("/rename", rename), web.post("/delete", delete), web.post("/fa", fa)])
    return app


if __name__ == "__main__":
    if "assets" in sys.argv:
        make_assets()
        sys.exit(0)
    if not TOKEN or not GUILD_ID:
        sys.exit("ضع DISCORD_TOKEN و GUILD_ID في ملف .env")
    bot.run(TOKEN)
