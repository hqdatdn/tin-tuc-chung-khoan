"""Hệ thống cập nhật tin tài chính - giai đoạn 1.

Cách chạy:
  python tin_tuc.py           lấy tin mới, lưu vào tin_tuc.db, gửi Telegram
  python tin_tuc.py --thu     chạy thử: lấy tin và in ra màn hình, không lưu, không gửi
  python tin_tuc.py --setup   lấy chat_id sau khi đã dán token vào bi_mat.ini và nhắn cho bot

Chạy trên máy (Task Scheduler) hoặc trên GitHub Actions (.github/workflows/tin_tuc.yml).
"""
import argparse
import configparser
import csv
import hashlib
import html
import json
import logging
import os
import re
import sqlite3
import sys
import unicodedata
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from logging.handlers import RotatingFileHandler
from pathlib import Path
from urllib.parse import quote_plus

import feedparser
import requests

THU_MUC = Path(__file__).resolve().parent
CONFIG = THU_MUC / "config.ini"
FILE_BI_MAT = THU_MUC / "bi_mat.ini"
DB = THU_MUC / "tin_tuc.db"
FILE_MA = THU_MUC / "ma_hose.csv"
FILE_TEN = THU_MUC / "ten_goi_khac.csv"
FILE_TEMPLATE = THU_MUC / "tin_tuc_template.html"
FILE_HTML = THU_MUC / "tin_tuc.html"
NGAY_HTML = 3          # trang HTML hiện tin trong bấy nhiêu ngày
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"}
VN_TZ = timezone(timedelta(hours=7))

LUU_TOI_DA_GIO = 48    # bỏ qua tin cũ hơn mức này
XOA_SAU_NGAY = 30      # kho tin chỉ giữ bấy nhiêu ngày cho gọn
GUI_TOI_DA_GIO = 12    # tin chưa gửi mà cũ hơn mức này thì không gửi nữa (sau khi máy tắt lâu)

GN_EN = "https://news.google.com/rss/search?hl=en-US&gl=US&ceid=US:en&q="
GN_VI = "https://news.google.com/rss/search?hl=vi&gl=VN&ceid=VN:vi&q="
# Google News chỉ lấy từ các báo này, tránh tin rác từ trang nhỏ
BAO_EN = "site:reuters.com OR site:bloomberg.com OR site:cnbc.com OR site:wsj.com OR site:ft.com OR site:kitco.com OR site:oilprice.com"
BAO_VI = "site:vneconomy.vn OR site:vietnambiz.vn OR site:thoibaonganhang.vn OR site:baochinhphu.vn OR site:sbv.gov.vn OR site:bnews.vn"

# (tên nguồn, url, nhóm, lọc). lọc=True: chỉ giữ tin có mã CK hoặc từ khóa quan trọng
NGUON = [
    ("CafeF", "https://cafef.vn/thi-truong-chung-khoan.rss", "ck", False),
    ("CafeF", "https://cafef.vn/doanh-nghiep.rss", "dn", False),
    ("CafeF", "https://cafef.vn/vi-mo-dau-tu.rss", "vm", True),
    ("CafeF", "https://cafef.vn/tai-chinh-ngan-hang.rss", "vm", False),
    ("CafeF", "https://cafef.vn/thi-truong.rss", "hh", True),
    ("CafeF", "https://cafef.vn/tai-chinh-quoc-te.rss", "qt", True),
    ("Vietstock", "https://vietstock.vn/830/chung-khoan/co-phieu.rss", "ck", False),
    ("Vietstock", "https://vietstock.vn/737/doanh-nghiep/hoat-dong-kinh-doanh.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/738/doanh-nghiep/co-tuc.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/739/chung-khoan/giao-dich-noi-bo.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/741/chung-khoan/niem-yet.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/764/doanh-nghiep/tang-von-m-a.rss", "dn", False),
    ("Vietstock", "https://vietstock.vn/145/chung-khoan/y-kien-chuyen-gia.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/1636/nhan-dinh-phan-tich/nhan-dinh-thi-truong.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/582/nhan-dinh-phan-tich/phan-tich-co-ban.rss", "cg", False),
    ("Vietstock", "https://vietstock.vn/143/chung-khoan/chinh-sach.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/761/kinh-te/vi-mo.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/757/tai-chinh/ngan-hang.rss", "vm", False),
    ("Vietstock", "https://vietstock.vn/2/hang-hoa.rss", "hh", False),
    ("Vietstock", "https://vietstock.vn/773/the-gioi/chung-khoan-the-gioi.rss", "qt", False),
    ("Vietstock", "https://vietstock.vn/772/the-gioi/tai-chinh-quoc-te.rss", "qt", False),
    ("TNCK", "https://tinnhanhchungkhoan.vn/rss/chung-khoan-2.rss", "ck", False),
    ("VnExpress", "https://vnexpress.net/rss/kinh-doanh.rss", "vm", True),
    ("Tuổi Trẻ", "https://tuoitre.vn/rss/kinh-doanh.rss", "vm", True),
    ("Thanh Niên", "https://thanhnien.vn/rss/kinh-te.rss", "vm", True),
    ("Google News", GN_VI + quote_plus(f'("Ngân hàng Nhà nước" OR "lãi suất" OR "tỷ giá" OR "chứng khoán") ({BAO_VI}) when:2d'), "vm", True),
    ("Fed", "https://www.federalreserve.gov/feeds/press_all.xml", "qt", True),
    ("CNBC", "https://www.cnbc.com/id/100003114/device/rss/rss.html", "qt", True),
    ("CNBC", "https://www.cnbc.com/id/10000664/device/rss/rss.html", "qt", True),
    ("MarketWatch", "https://feeds.content.dowjones.io/public/rss/mw_topstories", "qt", True),
    ("Google News", GN_EN + quote_plus(f'("Federal Reserve" OR FOMC OR "oil prices" OR "gold prices" OR "copper prices" OR Vietnam) ({BAO_EN}) when:1d'), "qt", False),
]

TEN_NHOM = {
    "dn": "🏢 Doanh nghiệp",
    "ck": "📈 Thị trường chứng khoán",
    "cg": "🗣 Nhận định - chuyên gia",
    "vm": "🏦 Vĩ mô - Tiền tệ",
    "hh": "🛢 Hàng hóa",
    "qt": "🌍 Quốc tế",
}

TU_KHOA_VN = [
    "lãi suất", "tỷ giá", "ngân hàng nhà nước", "nhnn", "lạm phát", "cpi", "gdp", "tín dụng",
    "fed", "trái phiếu", "giá vàng", "vàng miếng", "giá dầu", "xăng dầu", "giá thép", "phân bón",
    "cao su", "cà phê", "giá gạo", "đầu tư công", "fdi", "xuất khẩu", "thuế quan", "chứng khoán",
    "vn-index", "vnindex", "khối ngoại", "nâng hạng", "margin", "cổ phiếu", "cổ tức",
]
TU_KHOA_EN = re.compile(
    r"\b(fed|federal reserve|fomc|powell|interest rates?|rate cut|rate hike|inflation|cpi|"
    r"treasur(y|ies)|bond yields?|oil|crude|opec|gold|copper|steel|iron ore|dollar|tariffs?|"
    r"china|vietnam|emerging markets?|s&p 500|nasdaq|dow|recession|payrolls?|jobs report)\b",
    re.I,
)

# Mã trùng với từ viết tắt thông dụng: chỉ nhận khi có "mã X", "cổ phiếu X", "(X)", "HOSE: X"
MA_DE_NHAM = {"VND", "HCM", "SBV", "SSC", "VIP", "COM", "GAS", "PET", "FIT", "ECO", "ICT",
              "VNG", "VPS", "SGN", "TCT", "NAV", "SMA", "ABS", "CCC"}
CHU = "A-Za-z0-9À-ỹ"
RE_MA = re.compile(rf"(?<![{CHU}])([A-Z][A-Z0-9]{{2}})(?![{CHU}])")

log = logging.getLogger("tin_tuc")


def cai_log():
    log.setLevel(logging.INFO)
    fh = RotatingFileHandler(THU_MUC / "tin_tuc.log", maxBytes=1_000_000, backupCount=2, encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    log.addHandler(fh)
    if sys.stdout:  # chạy bằng pythonw (ẩn cửa sổ) thì không có stdout
        log.addHandler(logging.StreamHandler(sys.stdout))


def doc_config():
    """config.ini (cài đặt, đưa lên GitHub được) + bi_mat.ini (token, chỉ nằm trên máy).
    Trên GitHub, token lấy từ biến môi trường TELEGRAM_TOKEN / TELEGRAM_CHAT_ID (GitHub Secrets)."""
    cfg = configparser.ConfigParser()
    cfg.read([CONFIG, FILE_BI_MAT], encoding="utf-8")
    if not cfg.has_section("telegram"):
        cfg.add_section("telegram")
    for khoa, bien in (("token", "TELEGRAM_TOKEN"), ("chat_id", "TELEGRAM_CHAT_ID")):
        if os.environ.get(bien):
            cfg.set("telegram", khoa, os.environ[bien].strip())
    return cfg


def doc_ma():
    with open(FILE_MA, encoding="utf-8") as f:
        return {r["ma"].strip().upper() for r in csv.DictReader(f)}


def doc_ten_goi():
    """Tên công ty hay xuất hiện trong bài báo -> mã, đọc từ ten_goi_khac.csv (bạn tự thêm được)."""
    if not FILE_TEN.exists():
        return []
    with open(FILE_TEN, encoding="utf-8") as f:
        return [(re.compile(rf"(?<![{CHU}]){re.escape(r['ten'].strip())}(?![{CHU}])", re.I),
                 r["ma"].strip().upper()) for r in csv.DictReader(f) if r["ten"].strip()]


def bo_dau(s):
    s = unicodedata.normalize("NFD", s.lower()).replace("đ", "d")
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return re.sub(r"[^a-z0-9]+", " ", s).strip()


def lam_sach(s):
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def tim_ma(text, tat_ca_ma, ten_goi):
    ma = [m for re_ten, m in ten_goi if re_ten.search(text)]
    ma = list(dict.fromkeys(ma))
    for m in RE_MA.findall(text):
        if m not in tat_ca_ma or m in ma:
            continue
        if m in MA_DE_NHAM and not re.search(rf"(?i:\(|mã\s+|cổ phiếu\s+|cp\s+|hose:\s*|hsx:\s*){m}(?![{CHU}])", text):
            continue
        ma.append(m)
    return ma


def doc_ngay(e):
    """Ngày đăng (UTC). Không đọc được ngày thì trả None để bỏ tin, tránh tin cũ bị coi là mới."""
    t = e.get("published_parsed") or e.get("updated_parsed")
    if t:
        return datetime(*t[:6], tzinfo=timezone.utc)
    s = e.get("published") or e.get("updated")
    if not s:
        return None
    try:
        # Một số báo ghi múi giờ "+07" thay vì "+0700"
        d = parsedate_to_datetime(re.sub(r"([+-]\d{2})$", r"\g<1>00", s.strip()))
        return d.astimezone(timezone.utc) if d.tzinfo else d.replace(tzinfo=VN_TZ).astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None


def lay_nguon(nguon):
    ten, url, nhom, loc = nguon
    try:
        r = requests.get(url, headers=UA, timeout=20)
        r.raise_for_status()
        return nguon, feedparser.parse(r.content).entries
    except Exception as e:
        log.warning("Lỗi nguồn %s %s: %s", ten, url, e)
        return nguon, []


def thu_thap(tat_ca_ma):
    """Đọc tất cả nguồn, trả về danh sách tin đã gắn mã và đánh dấu giữ/bỏ."""
    ten_goi = doc_ten_goi()
    gioi_han = datetime.now(timezone.utc) - timedelta(hours=LUU_TOI_DA_GIO)
    tin = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        ket_qua = list(ex.map(lay_nguon, NGUON))
    trong = sorted({f"{n[0]} ({n[1].split('/')[2]})" for n, entries in ket_qua if not entries})
    if trong:
        log.warning("Nguồn không lấy được tin: %s", ", ".join(trong))
    for (ten, url, nhom, loc), entries in ket_qua:
        for e in entries:
            tieu_de = lam_sach(e.get("title"))
            link = e.get("link", "")
            if not tieu_de or not link:
                continue
            nguon = ten
            if ten == "Google News":
                src = e.get("source", {}).get("title")
                if src:
                    nguon = src
                    tieu_de = re.sub(rf"\s+-\s+{re.escape(src)}$", "", tieu_de)
            thoi_gian = doc_ngay(e)
            if thoi_gian is None or thoi_gian < gioi_han:
                continue
            tom_tat = lam_sach(e.get("summary"))[:400]
            noi_dung = f"{tieu_de} {tom_tat}"
            ma = tim_ma(noi_dung, tat_ca_ma, ten_goi) if nhom != "qt" else []
            nhom_tin = nhom
            if loc:
                thap = noi_dung.lower()
                if ".vn/" in url:
                    giu = bool(ma) or any(k in thap for k in TU_KHOA_VN)
                else:
                    giu = bool(TU_KHOA_EN.search(noi_dung))
                if ma and nhom == "vm":
                    nhom_tin = "dn"
            else:
                giu = True
            tin.append({
                "id": hashlib.sha1(link.encode()).hexdigest(),
                "khoa_td": bo_dau(tieu_de),
                "nguon": nguon, "nhom": nhom_tin, "tieu_de": tieu_de, "link": link,
                "tom_tat": tom_tat, "ma": ",".join(ma),
                "thoi_gian": thoi_gian.isoformat(), "giu": int(giu),
            })
    return tin


def mo_db():
    con = sqlite3.connect(DB)
    con.execute("""CREATE TABLE IF NOT EXISTS tin (
        id TEXT PRIMARY KEY, khoa_td TEXT, nguon TEXT, nhom TEXT, tieu_de TEXT, link TEXT,
        tom_tat TEXT, ma TEXT, thoi_gian TEXT, lay_luc TEXT, giu INTEGER, da_gui INTEGER DEFAULT 0)""")
    con.execute("CREATE INDEX IF NOT EXISTS ix_khoa ON tin(khoa_td)")
    con.execute("CREATE INDEX IF NOT EXISTS ix_ma ON tin(ma)")
    # dich: 0 = chưa xét, 1 = đã dịch sang tiếng Việt, 2 = tin tiếng Việt, không cần dịch
    if "dich" not in {r[1] for r in con.execute("PRAGMA table_info(tin)")}:
        con.execute("ALTER TABLE tin ADD COLUMN dich INTEGER DEFAULT 0")
    return con


def luu(con, tin):
    """Lưu tin mới, bỏ tin trùng link hoặc trùng tiêu đề (nhiều báo đăng lại). Trả về số tin mới."""
    moi = 0
    bay_gio = datetime.now(timezone.utc).isoformat()
    for t in tin:
        if con.execute("SELECT 1 FROM tin WHERE id=? OR khoa_td=?", (t["id"], t["khoa_td"])).fetchone():
            continue
        con.execute("INSERT INTO tin (id,khoa_td,nguon,nhom,tieu_de,link,tom_tat,ma,thoi_gian,lay_luc,giu,da_gui,dich) "
                    "VALUES (:id,:khoa_td,:nguon,:nhom,:tieu_de,:link,:tom_tat,:ma,:thoi_gian,:lay_luc,:giu,0,0)",
                    {**t, "lay_luc": bay_gio})
        moi += 1
    con.commit()
    return moi


def trong_gio_yen_lang(cfg):
    khoang = cfg.get("cai_dat", "gio_yen_lang", fallback="").strip()
    if not khoang:
        return False
    a, b = (int(x) for x in khoang.split("-"))
    h = datetime.now(VN_TZ).hour
    return a <= h < b if a < b else (h >= a or h < b)


def rut_gon_sapo(tom_tat, tieu_de, toi_da=220):
    """Sapo ngắn gọn để hiện dưới tiêu đề. Bỏ khi nguồn chỉ lặp lại tiêu đề (Google News, Fed)."""
    s = (tom_tat or "").strip()
    if bo_dau(s).startswith(bo_dau(tieu_de)):
        s = s[len(tieu_de):].strip()
    if len(s) < 40:
        return ""
    if len(s) > toi_da:
        s = s[:toi_da].rsplit(" ", 1)[0].rstrip(",.;:") + "…"
    return s


RE_TIENG_VIET = re.compile(r"[àáạảãâầấậẩẫăằắặẳẵèéẹẻẽêềếệểễìíịỉĩòóọỏõôồốộổỗơờớợởỡùúụủũưừứựửữỳýỵỷỹđ]", re.I)


def dich(text):
    """Dịch sang tiếng Việt bằng Google Dịch (bản miễn phí). Lỗi thì trả None để giữ nguyên bản gốc."""
    try:
        r = requests.get("https://translate.googleapis.com/translate_a/single", timeout=15, params={
            "client": "gtx", "sl": "auto", "tl": "vi", "dt": "t", "q": text})
        r.raise_for_status()
        return "".join(seg[0] for seg in r.json()[0] if seg[0])
    except Exception as e:
        log.warning("Không dịch được: %s", e)
        return None


def dich_tin_nuoc_ngoai(con):
    """Tin giữ lại mà tiêu đề không có dấu tiếng Việt thì dịch tiêu đề và sapo, ghi đè vào kho tin.
    Dịch lỗi thì để dich=0, lần chạy sau thử lại."""
    han = (datetime.now(timezone.utc) - timedelta(hours=LUU_TOI_DA_GIO)).isoformat()
    da_dich = 0
    for id_, tieu_de, tom_tat in con.execute(
            "SELECT id, tieu_de, tom_tat FROM tin WHERE giu=1 AND dich=0 AND thoi_gian>=?", (han,)).fetchall():
        if RE_TIENG_VIET.search(tieu_de):
            con.execute("UPDATE tin SET dich=2 WHERE id=?", (id_,))
            continue
        sapo = rut_gon_sapo(tom_tat, tieu_de, toi_da=400)
        ban_dich = dich(tieu_de + ("\n" + sapo if sapo else ""))
        if not ban_dich:
            continue
        dong = ban_dich.split("\n", 1)
        con.execute("UPDATE tin SET tieu_de=?, tom_tat=?, dich=1 WHERE id=?",
                    (dong[0].strip(), dong[1].strip() if len(dong) > 1 else "", id_))
        da_dich += 1
    con.commit()
    if da_dich:
        log.info("Đã dịch %d tin nước ngoài", da_dich)


def xuat_html(con, cfg):
    """Ghi tin_tuc.html: tin đã giữ trong NGAY_HTML ngày gần nhất, nhúng dữ liệu vào tin_tuc_template.html."""
    han = (datetime.now(timezone.utc) - timedelta(days=NGAY_HTML)).isoformat()
    tin = [{
        "t": r["thoi_gian"], "lay": r["lay_luc"], "nhom": r["nhom"], "td": r["tieu_de"], "link": r["link"],
        "sapo": rut_gon_sapo(r["tom_tat"], r["tieu_de"], toi_da=320), "ma": [m for m in r["ma"].split(",") if m],
        "nguon": r["nguon"], "dich": r["dich"] == 1,
    } for r in con.execute("SELECT * FROM tin WHERE giu=1 AND thoi_gian>=? ORDER BY thoi_gian DESC", (han,))]
    du_lieu = {
        "cap_nhat": datetime.now(timezone.utc).isoformat(),
        "uu_tien": [m.strip().upper() for m in cfg.get("cai_dat", "ma_uu_tien", fallback="").split(",") if m.strip()],
        "nhom": TEN_NHOM,
        "tin": tin,
    }
    json_str = json.dumps(du_lieu, ensure_ascii=False).replace("</", "<\\/")
    trang = FILE_TEMPLATE.read_text(encoding="utf-8").replace("/*DU_LIEU*/null", json_str)
    tam = FILE_HTML.with_suffix(".tmp")
    tam.write_text(trang, encoding="utf-8")
    tam.replace(FILE_HTML)  # ghi xong mới thay, trình duyệt không đọc phải file dở dang


def soan_tin(rows, uu_tien, nhom_gui):
    """Ghép tin thành các tin nhắn Telegram (HTML, mỗi tin nhắn < 4000 ký tự)."""
    nhom = {}
    for r in rows:
        ma = [m for m in r["ma"].split(",") if m]
        khoa = "uu" if set(ma) & uu_tien else r["nhom"]
        if khoa != "uu" and khoa not in nhom_gui:
            continue
        nhom.setdefault(khoa, []).append(r)
    if not nhom:
        return [], 0
    gio = datetime.now(VN_TZ).strftime("%H:%M %d/%m")
    tong = sum(len(v) for v in nhom.values())
    dong = [f"<b>📰 Tin mới {gio} — {tong} tin</b>"]
    thu_tu = ["uu", "dn", "ck", "cg", "vm", "hh", "qt"]
    for k in thu_tu:
        if k not in nhom:
            continue
        dong.append("")
        dong.append(f"<b>{'⭐ Mã ưu tiên' if k == 'uu' else TEN_NHOM[k]}</b>")
        for r in nhom[k]:
            ma = f"<b>[{r['ma'].replace(',', ' ')}]</b> " if r["ma"] else ""
            nguon = r["nguon"] + (" · dịch máy" if r["dich"] == 1 else "")
            dong.append(f"• {ma}<a href=\"{html.escape(r['link'])}\">{html.escape(r['tieu_de'])}</a>"
                        f" <i>({html.escape(nguon)})</i>")
            sapo = rut_gon_sapo(r["tom_tat"], r["tieu_de"])
            if sapo:
                dong.append(f"   ↳ {html.escape(sapo)}")
    tin_nhan, hien_tai = [], ""
    for d in dong:
        if len(hien_tai) + len(d) + 1 > 3900:
            tin_nhan.append(hien_tai)
            hien_tai = ""
        hien_tai += d + "\n"
    if hien_tai.strip():
        tin_nhan.append(hien_tai)
    return tin_nhan, tong


def gui_telegram(cfg, text):
    token = cfg.get("telegram", "token", fallback="").strip()
    chat_id = cfg.get("telegram", "chat_id", fallback="").strip()
    if not token or not chat_id:
        return False
    r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage", timeout=20, data={
        "chat_id": chat_id, "text": text, "parse_mode": "HTML", "disable_web_page_preview": "true"})
    if not r.ok:
        log.error("Telegram lỗi %s: %s", r.status_code, r.text[:200])
    return r.ok


def chay(cfg):
    tat_ca_ma = doc_ma()
    con = mo_db()
    con.row_factory = sqlite3.Row
    lan_dau = con.execute("SELECT COUNT(*) FROM tin").fetchone()[0] == 0
    tin = thu_thap(tat_ca_ma)
    moi = luu(con, tin)
    log.info("Đọc %d tin, %d tin mới", len(tin), moi)
    con.execute("DELETE FROM tin WHERE thoi_gian < ?",
                ((datetime.now(timezone.utc) - timedelta(days=XOA_SAU_NGAY)).isoformat(),))
    con.commit()
    dich_tin_nuoc_ngoai(con)
    try:
        xuat_html(con, cfg)
    except Exception:
        log.exception("Lỗi xuất HTML (vẫn gửi Telegram bình thường)")

    if lan_dau:
        # Lần chạy đầu: chỉ ghi nhận tin đang có, không gửi dồn hàng trăm tin cũ
        con.execute("UPDATE tin SET da_gui=1")
        con.commit()
        gui_telegram(cfg, f"✅ Hệ thống tin tức đã khởi động, ghi nhận {moi} tin hiện có. "
                          f"Từ lần chạy sau sẽ gửi tin mới.")
        return

    han = (datetime.now(timezone.utc) - timedelta(hours=GUI_TOI_DA_GIO)).isoformat()
    con.execute("UPDATE tin SET da_gui=1 WHERE da_gui=0 AND (giu=0 OR thoi_gian<?)", (han,))
    con.commit()
    if trong_gio_yen_lang(cfg):
        log.info("Đang trong giờ yên lặng, để dành tin")
        return

    rows = con.execute("SELECT * FROM tin WHERE da_gui=0 ORDER BY thoi_gian").fetchall()
    uu_tien = {m.strip().upper() for m in cfg.get("cai_dat", "ma_uu_tien", fallback="").split(",") if m.strip()}
    nhom_gui = {n.strip() for n in cfg.get("cai_dat", "nhom_gui", fallback=",".join(TEN_NHOM)).split(",")}
    tin_nhan, tong = soan_tin(rows, uu_tien, nhom_gui)
    for t in tin_nhan:
        if not gui_telegram(cfg, t):
            log.warning("Chưa gửi được Telegram (chưa cấu hình hoặc lỗi mạng), sẽ thử lại lần sau")
            return
    con.execute("UPDATE tin SET da_gui=1 WHERE da_gui=0")
    con.commit()
    log.info("Đã gửi %d tin trong %d tin nhắn", tong, len(tin_nhan))


def chay_thu():
    tin = thu_thap(doc_ma())
    giu = [t for t in tin if t["giu"]]
    print(f"Đọc {len(tin)} tin, giữ {len(giu)} tin\n")
    for k, ten in TEN_NHOM.items():
        nhom = [t for t in giu if t["nhom"] == k]
        print(f"== {ten}: {len(nhom)} tin")
        for t in nhom[:5]:
            print(f"   [{t['ma']}] {t['tieu_de'][:90]} ({t['nguon']})")


def setup(cfg):
    token = cfg.get("telegram", "token", fallback="").strip()
    if not token:
        print("Chưa có token. Tạo file bi_mat.ini với 2 dòng:\n[telegram]\ntoken = <token của bot>\nrồi chạy lại.")
        return
    r = requests.get(f"https://api.telegram.org/bot{token}/getUpdates", timeout=20).json()
    if not r.get("ok"):
        print("Token không đúng:", r.get("description"))
        return
    chats = [u["message"]["chat"] for u in r["result"] if "message" in u]
    if not chats:
        print("Bot chưa nhận được tin nhắn nào. Mở Telegram, tìm bot của bạn, bấm Start "
              "hoặc gửi một chữ bất kỳ, rồi chạy lại lệnh này.")
        return
    chat = chats[-1]
    cfg.set("telegram", "chat_id", str(chat["id"]))
    FILE_BI_MAT.write_text(
        "# File bí mật: KHÔNG chia sẻ, KHÔNG đưa lên GitHub (đã có trong .gitignore)\n"
        f"[telegram]\ntoken = {token}\nchat_id = {chat['id']}\n", encoding="utf-8")
    ten = chat.get("first_name") or chat.get("title") or ""
    print(f"Đã lưu chat_id {chat['id']} ({ten}).")
    if gui_telegram(cfg, "✅ Kết nối thành công! Bot tin tức sẽ gửi tin vào đây."):
        print("Đã gửi tin nhắn thử, hãy kiểm tra Telegram.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--thu", action="store_true")
    ap.add_argument("--setup", action="store_true")
    a = ap.parse_args()
    if sys.stdout:
        sys.stdout.reconfigure(encoding="utf-8")
    cfg = doc_config()
    if a.setup:
        setup(cfg)
    elif a.thu:
        chay_thu()
    else:
        cai_log()
        try:
            chay(cfg)
        except Exception:
            log.exception("Lỗi khi chạy")


if __name__ == "__main__":
    main()
