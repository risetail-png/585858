#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
bridge_pdf_link_app.py
======================
橋梁定期点検PDF ナビゲーションボタン追加ツール
v9: 複数ファイル一括処理対応

起動方法:
    python bridge_pdf_link_app.py

必要ライブラリ:
    pip install pikepdf pypdf Pillow
    ※ tkinterdnd2 はドラッグ＆ドロップ用（任意）
"""

import io
import os
import queue
import re
import sys
import threading
import tkinter as tk
from collections import defaultdict
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

# ── オプション依存 ────────────────────────────────────────────────────────────
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    HAS_DND = True
except ImportError:
    HAS_DND = False

# ── 必須ライブラリチェック ────────────────────────────────────────────────────
MISSING = []
try:
    import pikepdf
    from pikepdf import Array, Dictionary, Name, Stream
except ImportError:
    MISSING.append("pikepdf")

try:
    import pypdf
except ImportError:
    MISSING.append("pypdf")

try:
    from PIL import Image, ImageDraw, ImageFont
except ImportError:
    MISSING.append("pillow")


# ═══════════════════════════════════════════════════════════════════════════════
#  定数
# ═══════════════════════════════════════════════════════════════════════════════

BTN_Y1, BTN_Y2 = 8.0, 34.0
BTN_H   = BTN_Y2 - BTN_Y1
BTN_GAP = 5.0
IMG_SCALE = 3

COLOR_FORWARD         = (46,  97, 184)
COLOR_OUTLINE_FORWARD = (20,  55, 130)
COLOR_BACK            = (34, 139,  69)
COLOR_OUTLINE_BACK    = (20,  90,  45)

KEYWORD_DIAGRAM = "データ記録様式(その９)"
KEYWORD_PHOTO   = "データ記録様式(その１０)"

# 定期点検記録様式 その１〜その１３
# 定期点検記録様式キーワード
KEYWORD_FORM1 = "定期点検記録様式(その１)"

# その１ページに追加するボタン対象 (番号 -> キーワード)
# その１〜その８: 定期点検記録様式
# その９: データ記録様式(損傷図)、径間ごとに別処理
# その１０〜その１３: データ記録様式
KEYWORDS_FORM_1_8 = {
    1: "定期点検記録様式(その１)",
    2: "定期点検記録様式(その２)",
    3: "定期点検記録様式(その３)",
    4: "定期点検記録様式(その４)",
    5: "定期点検記録様式(その５)",
    6: "定期点検記録様式(その６)",
    7: "定期点検記録様式(その７)",
    8: "定期点検記録様式(その８)",
}
KEYWORDS_FORM_10_13 = {
    10: "データ記録様式(その１０)",
    11: "データ記録様式(その１１)",
    12: "データ記録様式(その１２)",
    13: "データ記録様式(その１３)",
}

COLOR_FORM         = (180,  90,  20)
COLOR_OUTLINE_FORM = (130,  60,  10)

RE_PHOTO_PAGE_NUM = re.compile(r'写真番号[\s　]*(\d+)((?:\s+\d+)*)')

SPAN_CELL_X_MIN = 385.0
SPAN_CELL_X_MAX = 430.0
SPAN_CELL_Y_MIN = 510.0
SPAN_CELL_Y_MAX = 540.0


# ═══════════════════════════════════════════════════════════════════════════════
#  ユーティリティ
# ═══════════════════════════════════════════════════════════════════════════════

def _normalize_text(text):
    text = text.translate(str.maketrans('０１２３４５６７８９', '0123456789'))
    return text.replace('－', '-').replace('―', '-')


def _parse_photo_page_nums(text):
    text = _normalize_text(text)
    work = text
    work = re.sub(r'\d{4}[./]\d{2}[./]\d{2}', '', work)
    work = re.sub(r'\d+\.\d+', '', work)
    work = re.sub(r'写真番号\s*\d+\s*[-－]\s*\d+\s*の\S+', '', work)
    work = re.sub(r'前回\s*[-－]?\s*\d*', '', work)
    work = re.sub(r'[-－]\s*\d+', '', work)
    nums = []
    for m in RE_PHOTO_PAGE_NUM.finditer(work):
        nums.append(int(m.group(1)))
        for extra in re.findall(r'\d+', m.group(2)):
            nums.append(int(extra))
    if not nums:
        return []
    base  = min(nums)
    upper = base + 15
    for m in re.finditer(r'\b(\d{1,2})\b', work):
        n = int(m.group(1))
        if base <= n <= upper:
            nums.append(n)
    return sorted(set(nums))


def find_japanese_font():
    candidates = [
        r"C:\Windows\Fonts\msgothic.ttc",
        r"C:\Windows\Fonts\meiryo.ttc",
        r"C:\Windows\Fonts\YuGothM.ttc",
        r"C:\Windows\Fonts\yugothm.ttc",
        "/System/Library/Fonts/ヒラギノ角ゴシック W3.ttc",
        "/System/Library/Fonts/Hiragino Sans GB.ttc",
        "/Library/Fonts/Osaka.ttf",
        "/usr/share/fonts/opentype/ipafont-gothic/ipag.ttf",
        "/usr/share/fonts/truetype/fonts-japanese-gothic.ttf",
        "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    ]
    for p in candidates:
        if os.path.exists(p):
            return p
    return None


# ═══════════════════════════════════════════════════════════════════════════════
#  ページ分類・径間番号取得
# ═══════════════════════════════════════════════════════════════════════════════

def classify_pages(pdf_path):
    """
    各ページを分類して返す。
    戻り値:
      diag_pages   : 損傷図ページ index リスト (その９)
      photo_pages  : 損傷写真ページ index リスト (その１０)
      form1_pages  : 定期点検記録様式(その１) index リスト
      form_first   : {番号: 最初のpage_idx} その２〜その８, その１０〜その１３
    """
    reader = pypdf.PdfReader(pdf_path)
    diag, photo, form1 = [], [], []
    form_first = {}   # num -> first page_idx

    for i, page in enumerate(reader.pages):
        text = page.extract_text() or ""

        if KEYWORD_DIAGRAM in text:
            diag.append(i)
        if KEYWORD_PHOTO in text:
            photo.append(i)
        if KEYWORD_FORM1 in text:
            form1.append(i)

        # その２〜その８
        for num, kw in KEYWORDS_FORM_1_8.items():
            if kw in text and num not in form_first:
                form_first[num] = i

        # その１０〜その１３
        for num, kw in KEYWORDS_FORM_10_13.items():
            if kw in text and num not in form_first:
                form_first[num] = i

    return diag, photo, form1, form_first


def get_span_number_from_page(page):
    """径間番号を文字列で返す（例: "1", "1-1", "1-2"）。見つからない場合は None。"""
    hits = []
    def visitor(text, cm, tm, fontdict, fontsize):
        x, y = tm[4], tm[5]
        t = text.strip()
        if (t and SPAN_CELL_X_MIN <= x <= SPAN_CELL_X_MAX
                and SPAN_CELL_Y_MIN <= y <= SPAN_CELL_Y_MAX):
            hits.append(t)
    page.extract_text(visitor_text=visitor)
    num_str = _normalize_text(''.join(hits))
    # N-M 形式（例: 1-1）または単純な数字
    m = re.search(r'\d+[-−]\d+|\d+', num_str)
    return m.group() if m else None


def get_span_number_fallback(text):
    """テキストから径間番号を文字列で返すフォールバック。"""
    text = _normalize_text(text)
    m = re.search(r'起点側\s*終点側\s*(\d+[-−]\d+|\d+)', text)
    return m.group(1) if m else None


# ═══════════════════════════════════════════════════════════════════════════════
#  ボタン描画・追加
# ═══════════════════════════════════════════════════════════════════════════════

def get_page_size(pdf, page_idx):
    mb = pdf.pages[page_idx]['/MediaBox']
    return float(mb[2]), float(mb[3])


def render_button_jpeg(btn_list, total_w_pt, btn_h_pt,
                       fill_color, outline_color, font_path):
    img_w = int(total_w_pt * IMG_SCALE)
    img_h = int(btn_h_pt  * IMG_SCALE)
    img   = Image.new('RGB', (img_w, img_h), (255, 255, 255))
    draw  = ImageDraw.Draw(img)
    n        = len(btn_list)
    gap_px   = int(BTN_GAP * IMG_SCALE)
    btn_w_px = (img_w - gap_px * (n + 1)) // n
    by_margin = int(2 * IMG_SCALE)
    bh        = img_h - int(4 * IMG_SCALE)
    padding_v = int(3 * IMG_SCALE)
    fsize = bh - padding_v * 2
    if font_path:
        for fs in range(fsize, 4, -1):
            try:
                fnt = ImageFont.truetype(font_path, fs)
            except Exception:
                fnt = ImageFont.load_default()
                break
            ok = True
            for label, _ in btn_list:
                bb = fnt.getbbox(label)
                tw, th = bb[2] - bb[0], bb[3] - bb[1]
                if th > bh - padding_v * 2 or tw > btn_w_px - int(4 * IMG_SCALE):
                    ok = False
                    break
            if ok:
                break
    else:
        fnt = ImageFont.load_default()
    for i, (label, _) in enumerate(btn_list):
        bx = gap_px + i * (btn_w_px + gap_px)
        draw.rounded_rectangle([bx, by_margin, bx + btn_w_px, by_margin + bh],
                               radius=int(4 * IMG_SCALE),
                               fill=fill_color, outline=outline_color, width=2)
        bb = fnt.getbbox(label)
        tw, th = bb[2] - bb[0], bb[3] - bb[1]
        draw.text((bx + (btn_w_px - tw) // 2, by_margin + (bh - th) // 2),
                  label, fill=(255, 255, 255), font=fnt)
    buf = io.BytesIO()
    img.save(buf, format='JPEG', quality=92)
    return buf.getvalue(), img_w, img_h


# 1行あたりの最大ボタン数（上端多段用）
BTN_ROW_MAX = 13
ROW_GAP     = 2.0   # 段間の隙間(pt)


def _place_button_row(pdf, page_idx, row_btn_list, page_w, y1, y2,
                      fill_color, outline_color, font_path, xobj_name):
    """1行分のボタン画像をページに描画しアノテーションを追加する（内部共通処理）。"""
    page      = pdf.pages[page_idx]
    margin_l  = 64.0
    margin_r  = page_w - 48.0
    btn_total = margin_r - margin_l
    btn_h     = y2 - y1

    jpeg_bytes, img_w, img_h = render_button_jpeg(
        row_btn_list, btn_total, btn_h, fill_color, outline_color, font_path)

    xobj = Stream(pdf, jpeg_bytes)
    xobj['/Type']             = Name('/XObject')
    xobj['/Subtype']          = Name('/Image')
    xobj['/Width']            = img_w
    xobj['/Height']           = img_h
    xobj['/ColorSpace']       = Name('/DeviceRGB')
    xobj['/BitsPerComponent'] = 8
    xobj['/Filter']           = Name('/DCTDecode')
    xobj_ref = pdf.make_indirect(xobj)

    if '/XObject' not in page['/Resources']:
        page['/Resources']['/XObject'] = pikepdf.Dictionary()
    page['/Resources']['/XObject'][xobj_name] = xobj_ref

    stream_content = (f"q\n{btn_total:.4f} 0 0 {btn_h:.4f} "
                      f"{margin_l:.4f} {y1:.4f} cm\n{xobj_name} Do\nQ\n").encode('latin-1')
    cstream = Stream(pdf, stream_content)
    existing = page['/Contents']
    page['/Contents'] = pikepdf.Array(
        (list(existing) if isinstance(existing, pikepdf.Array) else [existing])
        + [pdf.make_indirect(cstream)]
    )

    n        = len(row_btn_list)
    btn_w_pt = (btn_total - BTN_GAP * (n + 1)) / n
    annots   = list(page.get('/Annots', pikepdf.Array()))
    for i, (_, target_idx) in enumerate(row_btn_list):
        bx1 = margin_l + BTN_GAP + i * (btn_w_pt + BTN_GAP)
        bx2 = bx1 + btn_w_pt
        dest = pikepdf.Array([pdf.pages[target_idx].obj, Name('/Fit')])
        annots.append(pdf.make_indirect(Dictionary(
            Type=Name('/Annot'), Subtype=Name('/Link'),
            Rect=Array([pikepdf.Real(bx1), pikepdf.Real(y1),
                        pikepdf.Real(bx2), pikepdf.Real(y2)]),
            Border=Array([pikepdf.Real(0)] * 3),
            Dest=dest, H=Name('/I'),
        )))
    page['/Annots'] = pikepdf.Array(annots)


BTN_ROW_MAX_BOTTOM = 8   # 青・緑ボタンの1行最大数


def add_buttons_bottom(pdf, page_idx, btn_list, page_w, page_h,
                       fill_color, outline_color, font_path, xobj_prefix):
    """青・緑ボタン用: ページ下端に配置。6個超で下方向に折り返す（2段目が1段目の下）。
    1段目: BTN_Y1+BTN_H+ROW_GAP 〜 BTN_Y1+BTN_H*2+ROW_GAP  （上）
    2段目: BTN_Y1               〜 BTN_Y1+BTN_H              （下・最下段）
    """
    rows = [btn_list[i:i+BTN_ROW_MAX_BOTTOM]
            for i in range(0, len(btn_list), BTN_ROW_MAX_BOTTOM)]
    num_rows = len(rows)
    for r, row in enumerate(rows):
        # r=0 が1段目（上）、r=num_rows-1 が最下段
        # 最下段のy1=BTN_Y1、上に行くほど y1 が大きくなる
        row_from_bottom = num_rows - 1 - r
        y1 = BTN_Y1 + row_from_bottom * (BTN_H + ROW_GAP)
        y2 = y1 + BTN_H
        _place_button_row(pdf, page_idx, row, page_w, y1, y2,
                          fill_color, outline_color, font_path,
                          f'/{xobj_prefix}{page_idx}r{r}')


def add_buttons_top(pdf, page_idx, btn_list, page_w, page_h,
                    fill_color, outline_color, font_path, xobj_prefix):
    """オレンジボタン用: ページ上端から多段配置（BTN_ROW_MAX 超で折り返し）。"""
    rows = [btn_list[i:i+BTN_ROW_MAX] for i in range(0, len(btn_list), BTN_ROW_MAX)]
    for r, row in enumerate(rows):
        # r=0 が最上段、r=1 がその下（PDFのY軸は下から上）
        y2 = page_h - r * (BTN_H + ROW_GAP)
        y1 = y2 - BTN_H
        _place_button_row(pdf, page_idx, row, page_w, y1, y2,
                          fill_color, outline_color, font_path,
                          f'/{xobj_prefix}{page_idx}r{r}')


# ═══════════════════════════════════════════════════════════════════════════════
#  1ファイル処理
# ═══════════════════════════════════════════════════════════════════════════════

def process_one(input_path, output_path, font_path, log_cb):
    """1つのPDFを処理してボタンを追加する。失敗時は例外を送出。"""
    diag_pages, photo_pages, form1_pages, form_first = classify_pages(input_path)

    if not diag_pages:
        raise RuntimeError(f"損傷図ページ（{KEYWORD_DIAGRAM}）が見つかりません。")
    if not photo_pages:
        raise RuntimeError(f"損傷写真ページ（{KEYWORD_PHOTO}）が見つかりません。")

    log_cb(f"  損傷図ページ  : {[p+1 for p in diag_pages]}")
    log_cb(f"  損傷写真ページ: {[p+1 for p in photo_pages]}")
    log_cb(f"  その１ページ  : {[p+1 for p in form1_pages]}")
    log_cb(f"  様式初頁      : { {k: v+1 for k, v in form_first.items()} }")

    reader = pypdf.PdfReader(input_path)
    diag_span  = {}
    photo_span = {}

    for pidx in diag_pages:
        span = get_span_number_from_page(reader.pages[pidx])
        if span is None:
            span = get_span_number_fallback(reader.pages[pidx].extract_text() or "")
        diag_span[pidx] = span

    for pidx in photo_pages:
        span = get_span_number_from_page(reader.pages[pidx])
        if span is None:
            span = get_span_number_fallback(reader.pages[pidx].extract_text() or "")
        photo_span[pidx] = span

    span_to_diag  = defaultdict(list)
    span_to_photo = defaultdict(list)
    for pidx, span in diag_span.items():
        if span is not None:
            span_to_diag[span].append(pidx)
    for pidx, span in photo_span.items():
        if span is not None:
            span_to_photo[span].append(pidx)

    def _span_sort_key(s):
        """径間番号を数値タプルでソート（例: "1-2" -> (1, 2), "2" -> (2, 0)）"""
        parts = re.split(r'[-−]', str(s))
        try:
            return tuple(int(p) for p in parts)
        except ValueError:
            return (0, 0)

    all_spans     = sorted(set(span_to_diag.keys()) | set(span_to_photo.keys()),
                           key=_span_sort_key)
    is_multi_span = len(all_spans) > 1
    log_cb(f"  径間: {all_spans}")

    # 損傷写真の写真番号取得（ラベル用）
    photo_page_nums = {}
    for pidx in photo_pages:
        text = reader.pages[pidx].extract_text() or ""
        photo_page_nums[pidx] = _parse_photo_page_nums(text)

    # その９ 径間ごとの最初のページ {span -> first_page_idx}
    span_to_first_diag = {}
    for span in all_spans:
        pages = sorted(span_to_diag.get(span, []))
        if pages:
            span_to_first_diag[span] = pages[0]

    pdf = pikepdf.open(input_path, allow_overwriting_input=True)

    # ── 1ページ目（PDF先頭ページ）にナビボタン（オレンジ）────────────────────
    first_page_idx = 0
    pw, ph = get_page_size(pdf, first_page_idx)
    btn_list = []

    # その１〜その８
    for num in sorted(KEYWORDS_FORM_1_8.keys()):
        if num in form_first:
            btn_list.append((f"その{num}", form_first[num]))

    # その９（径間ごと）
    for span in all_spans:
        if span in span_to_first_diag:
            label = f"その9-{span}" if len(all_spans) > 1 else "その9"
            btn_list.append((label, span_to_first_diag[span]))

    # その１０〜その１３
    for num in sorted(KEYWORDS_FORM_10_13.keys()):
        if num in form_first:
            btn_list.append((f"その{num}", form_first[num]))

    if btn_list:
        log_cb(f"  1ページ目 → ボタン{len(btn_list)}個: {[b[0] for b in btn_list]}")
        add_buttons_top(pdf, first_page_idx, btn_list, pw, ph,
                        COLOR_FORM, COLOR_OUTLINE_FORM,
                        font_path, 'FormBtn')

    # ── 損傷図 → 損傷写真（青ボタン）────────────────────────────────────────
    for didx in diag_pages:
        span = diag_span.get(didx)
        if span is None:
            continue
        target_photo_pages = span_to_photo.get(span, [])
        if not target_photo_pages:
            continue
        pw, ph = get_page_size(pdf, didx)
        btn_list = []
        for pp in sorted(target_photo_pages):
            pp_span   = photo_span.get(pp)
            page_nums = photo_page_nums.get(pp, [])
            if page_nums:
                nums_str = (f"{min(page_nums)}〜{max(page_nums)}"
                            if len(page_nums) > 1 else f"{page_nums[0]}")
                if is_multi_span and pp_span:
                    # N-M形式（例: "1-1"）の場合は径間番号と写真番号をスペースで区切る
                    # 整数形式（例: "1"）の場合は従来通り "1-1〜3"
                    if re.search(r'\d+-\d+', str(pp_span)):
                        label = f"{pp_span}\u3000{nums_str}"   # 全角スペース区切り
                    else:
                        label = (f"{pp_span}-{nums_str}" if len(page_nums) > 1
                                 else f"{pp_span}-{page_nums[0]}")
                else:
                    label = nums_str
            else:
                label = (f"{pp_span}径間・p.{pp+1}"
                         if (is_multi_span and pp_span) else f"p.{pp+1}")
            btn_list.append((label, pp))
        add_buttons_bottom(pdf, didx, btn_list, pw, ph,
                           COLOR_FORWARD, COLOR_OUTLINE_FORWARD,
                           font_path, 'FwdBtn')

    # ── 損傷写真 → 損傷図（緑ボタン）────────────────────────────────────────
    for pp in photo_pages:
        span = photo_span.get(pp)
        if span is None:
            continue
        target_diag_pages = span_to_diag.get(span, [])
        if not target_diag_pages:
            continue
        pw, ph = get_page_size(pdf, pp)
        btn_list = []
        for didx in sorted(target_diag_pages):
            pp_span = photo_span.get(pp)
            label = (f"{pp_span}径間・p.{didx+1}"
                     if (is_multi_span and pp_span) else f"p.{didx+1}")
            btn_list.append((label, didx))
        add_buttons_bottom(pdf, pp, btn_list, pw, ph,
                           COLOR_BACK, COLOR_OUTLINE_BACK,
                           font_path, 'BackBtn')

    pdf.save(output_path)


# ═══════════════════════════════════════════════════════════════════════════════
#  複数ファイル一括処理（バックグラウンドスレッド）
# ═══════════════════════════════════════════════════════════════════════════════

def run_batch(file_list, log_cb, progress_cb, done_cb):
    """file_list: [input_path, ...] → 各ファイルと同フォルダに _linked.pdf を出力"""
    try:
        font_path = find_japanese_font()
        if not font_path:
            raise RuntimeError(
                "日本語フォントが見つかりません。\n"
                "MS ゴシック / ヒラギノ / IPAフォント等をインストールしてください。")
        log_cb(f"フォント: {Path(font_path).name}")

        total   = len(file_list)
        ok_list = []
        ng_list = []

        for i, inp in enumerate(file_list, 1):
            inp = str(inp)
            stem = Path(inp).stem
            out  = str(Path(inp).parent / f"{stem}_linked.pdf")
            log_cb("=" * 48)
            log_cb(f"[{i}/{total}] {Path(inp).name}")
            progress_cb(i, total)
            try:
                process_one(inp, out, font_path, log_cb)
                sz = os.path.getsize(out) / 1024 / 1024
                log_cb(f"  → 保存完了: {Path(out).name}  ({sz:.1f} MB)")
                ok_list.append(Path(inp).name)
            except Exception as e:
                import traceback
                log_cb(f"  エラー: {e}")
                log_cb(traceback.format_exc())
                ng_list.append((Path(inp).name, str(e)))

        log_cb("=" * 48)
        log_cb(f"完了: 成功 {len(ok_list)} / 失敗 {len(ng_list)} / 合計 {total}")
        done_cb(ok_list, ng_list)

    except Exception as e:
        import traceback
        log_cb(f"致命的エラー: {e}")
        log_cb(traceback.format_exc())
        done_cb([], [(str(e), str(e))])


# ═══════════════════════════════════════════════════════════════════════════════
#  GUI
# ═══════════════════════════════════════════════════════════════════════════════

class App(tk.Tk if not HAS_DND else TkinterDnD.Tk):

    BG      = "#1a1f2e"
    PANEL   = "#242938"
    BORDER  = "#2e3548"
    ACCENT  = "#4a7fe8"
    TEXT    = "#e8ecf4"
    SUBTEXT = "#8892aa"
    SUCCESS = "#22a06b"
    ERROR   = "#e8516a"
    WARNING = "#f0a040"
    BTN_HOV = "#5a8ff8"

    def __init__(self):
        super().__init__()
        self.title("橋梁点検PDF リンク追加ツール")
        self.geometry("780x620")
        self.minsize(680, 520)
        self.configure(bg=self.BG)
        self.resizable(True, True)

        self._file_list   = []   # 処理対象ファイルパスのリスト
        self._status      = tk.StringVar(value="PDFファイルを追加してください")
        self._log_queue   = queue.Queue()
        self._processing  = False

        self._build_ui()
        self._poll_log()

        if MISSING:
            self._show_missing()

    # ── UI構築 ────────────────────────────────────────────────────────────────
    def _build_ui(self):
        self.columnconfigure(0, weight=1)
        self.rowconfigure(1, weight=1)

        # ヘッダー
        hdr = tk.Frame(self, bg=self.BG)
        hdr.grid(row=0, column=0, sticky="ew", padx=24, pady=(20, 0))
        tk.Label(hdr, text="橋梁点検PDF", font=("Yu Gothic UI", 10),
                 fg=self.SUBTEXT, bg=self.BG).pack(anchor="w")
        tk.Label(hdr, text="リンク追加ツール",
                 font=("Yu Gothic UI Bold", 20, "bold"),
                 fg=self.TEXT, bg=self.BG).pack(anchor="w")
        tk.Label(hdr,
                 text="径間番号をもとに、損傷図（その９）↔ 損傷写真（その１０）間にナビゲーションボタンを自動追加します",
                 font=("Yu Gothic UI", 9), fg=self.SUBTEXT, bg=self.BG
                 ).pack(anchor="w", pady=(2, 0))
        legend = tk.Frame(hdr, bg=self.BG)
        legend.pack(anchor="w", pady=(4, 0))
        tk.Label(legend, text="■", fg="#4a7fe8", bg=self.BG,
                 font=("Yu Gothic UI", 9)).pack(side="left")
        tk.Label(legend, text="損傷図→損傷写真  ",
                 fg=self.SUBTEXT, bg=self.BG, font=("Yu Gothic UI", 9)).pack(side="left")
        tk.Label(legend, text="■", fg="#22a06b", bg=self.BG,
                 font=("Yu Gothic UI", 9)).pack(side="left")
        tk.Label(legend, text="損傷写真→損傷図  ／  出力は各PDFと同じフォルダに _linked.pdf で保存",
                 fg=self.SUBTEXT, bg=self.BG, font=("Yu Gothic UI", 9)).pack(side="left")

        tk.Frame(self, bg=self.BORDER, height=1).grid(
            row=0, column=0, sticky="ew", padx=24, pady=(88, 0))

        # メインパネル
        main = tk.Frame(self, bg=self.BG)
        main.grid(row=1, column=0, sticky="nsew", padx=24, pady=16)
        main.columnconfigure(0, weight=1)
        main.rowconfigure(1, weight=1)

        # ── ファイルリストエリア ──
        file_frame = tk.Frame(main, bg=self.PANEL,
                              highlightbackground=self.BORDER,
                              highlightthickness=1)
        file_frame.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        file_frame.columnconfigure(0, weight=1)

        # ドロップゾーン
        self._drop_zone = tk.Label(
            file_frame,
            text="📂  ここにPDFをドラッグ＆ドロップ（複数可）\nまたはクリックして選択",
            font=("Yu Gothic UI", 10), fg=self.SUBTEXT, bg=self.PANEL,
            cursor="hand2", pady=16
        )
        self._drop_zone.grid(row=0, column=0, columnspan=2,
                             sticky="ew", padx=16, pady=(12, 4))
        self._drop_zone.bind("<Button-1>", lambda e: self._browse_files())
        self._drop_zone.bind("<Enter>",
            lambda e: self._drop_zone.configure(fg=self.ACCENT))
        self._drop_zone.bind("<Leave>",
            lambda e: self._drop_zone.configure(fg=self.SUBTEXT))

        if HAS_DND:
            self._drop_zone.drop_target_register(DND_FILES)
            self._drop_zone.dnd_bind('<<Drop>>', self._on_drop)

        # ファイルリストボックス
        list_wrap = tk.Frame(file_frame, bg=self.PANEL)
        list_wrap.grid(row=1, column=0, sticky="ew", padx=16, pady=(0, 4))
        list_wrap.columnconfigure(0, weight=1)

        self._listbox = tk.Listbox(
            list_wrap, height=5,
            bg="#131720", fg=self.TEXT,
            font=("Yu Gothic UI", 9),
            selectbackground=self.ACCENT,
            relief="flat", bd=0,
            activestyle="none",
        )
        self._listbox.grid(row=0, column=0, sticky="ew")
        sb = ttk.Scrollbar(list_wrap, command=self._listbox.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self._listbox['yscrollcommand'] = sb.set

        # ファイル操作ボタン行
        btn_row = tk.Frame(file_frame, bg=self.PANEL)
        btn_row.grid(row=2, column=0, sticky="e", padx=16, pady=(0, 10))
        self._mk_small_btn(btn_row, "追加…",     self._browse_files).pack(side="left", padx=(0, 6))
        self._mk_small_btn(btn_row, "選択削除",  self._remove_selected).pack(side="left", padx=(0, 6))
        self._mk_small_btn(btn_row, "全クリア",  self._clear_files).pack(side="left")

        # ── ログエリア ──
        log_frame = tk.Frame(main, bg=self.PANEL,
                             highlightbackground=self.BORDER,
                             highlightthickness=1)
        log_frame.grid(row=1, column=0, sticky="nsew", pady=(0, 0))
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(1, weight=1)

        tk.Label(log_frame, text="処理ログ",
                 font=("Yu Gothic UI", 9), fg=self.SUBTEXT, bg=self.PANEL
                 ).grid(row=0, column=0, sticky="w", padx=12, pady=(8, 2))

        self._log = tk.Text(
            log_frame, bg="#131720", fg=self.SUBTEXT,
            font=("Consolas", 9), relief="flat", bd=0,
            state="disabled", wrap="word",
            insertbackground=self.TEXT,
            selectbackground=self.ACCENT,
        )
        self._log.grid(row=1, column=0, sticky="nsew", padx=8, pady=(0, 8))
        log_sb = ttk.Scrollbar(log_frame, command=self._log.yview)
        log_sb.grid(row=1, column=1, sticky="ns", pady=(0, 8), padx=(0, 4))
        self._log['yscrollcommand'] = log_sb.set

        self._log.tag_configure("info",    foreground=self.SUBTEXT)
        self._log.tag_configure("success", foreground=self.SUCCESS)
        self._log.tag_configure("error",   foreground=self.ERROR)
        self._log.tag_configure("warn",    foreground=self.WARNING)
        self._log.tag_configure("accent",  foreground=self.ACCENT)

        # ── フッター ──
        footer = tk.Frame(self, bg=self.BG)
        footer.grid(row=2, column=0, sticky="ew", padx=24, pady=(0, 16))
        footer.columnconfigure(0, weight=1)

        tk.Label(footer, textvariable=self._status,
                 font=("Yu Gothic UI", 9), fg=self.SUBTEXT, bg=self.BG,
                 anchor="w").grid(row=0, column=0, sticky="w")

        self._progress = ttk.Progressbar(footer, mode='determinate', length=200)
        self._progress.grid(row=0, column=1, padx=(12, 12))

        self._run_btn = tk.Button(
            footer, text="▶  処理開始",
            font=("Yu Gothic UI Bold", 10, "bold"),
            fg="white", bg=self.ACCENT,
            activeforeground="white", activebackground=self.BTN_HOV,
            relief="flat", bd=0, padx=20, pady=8,
            cursor="hand2", command=self._start
        )
        self._run_btn.grid(row=0, column=2)
        self._run_btn.bind("<Enter>",
            lambda e: self._run_btn.configure(bg=self.BTN_HOV))
        self._run_btn.bind("<Leave>",
            lambda e: self._run_btn.configure(bg=self.ACCENT))

    def _mk_small_btn(self, parent, text, cmd):
        return tk.Button(parent, text=text,
                         font=("Yu Gothic UI", 9),
                         fg=self.TEXT, bg=self.BORDER,
                         activeforeground=self.TEXT, activebackground=self.ACCENT,
                         relief="flat", bd=0, padx=10, pady=3,
                         cursor="hand2", command=cmd)

    # ── ファイル操作 ──────────────────────────────────────────────────────────
    def _browse_files(self):
        paths = filedialog.askopenfilenames(
            title="入力PDFを選択（複数可）",
            filetypes=[("PDFファイル", "*.pdf"), ("すべてのファイル", "*.*")]
        )
        if paths:
            self._add_files(list(paths))

    def _on_drop(self, event):
        # tkinterdnd2 は複数ファイルを "{path1} {path2}" または "path1 path2" 形式で返す
        raw = event.data.strip()
        # {} で囲まれたパス（スペース含む）を先に抽出
        paths = re.findall(r'\{([^}]+)\}', raw)
        # 残りのスペース区切りパスを追加
        remaining = re.sub(r'\{[^}]+\}', '', raw).split()
        paths += remaining
        pdf_paths = [p for p in paths if p.lower().endswith('.pdf')]
        if pdf_paths:
            self._add_files(pdf_paths)
        else:
            self._log_msg("PDFファイルをドロップしてください", "warn")

    def _add_files(self, paths):
        added = 0
        for p in paths:
            if p not in self._file_list:
                self._file_list.append(p)
                self._listbox.insert(tk.END, Path(p).name)
                added += 1
        if added:
            n = len(self._file_list)
            self._drop_zone.configure(
                text=f"📄  {n} 件のPDFが追加されています（クリックで追加選択）",
                fg=self.ACCENT)
            self._status.set(f"{n} 件のファイルが登録されています")

    def _remove_selected(self):
        sel = list(self._listbox.curselection())
        for i in reversed(sel):
            self._listbox.delete(i)
            self._file_list.pop(i)
        n = len(self._file_list)
        if n == 0:
            self._reset_drop_zone()
        else:
            self._status.set(f"{n} 件のファイルが登録されています")

    def _clear_files(self):
        self._file_list.clear()
        self._listbox.delete(0, tk.END)
        self._reset_drop_zone()

    def _reset_drop_zone(self):
        self._drop_zone.configure(
            text="📂  ここにPDFをドラッグ＆ドロップ（複数可）\nまたはクリックして選択",
            fg=self.SUBTEXT)
        self._status.set("PDFファイルを追加してください")

    # ── 処理実行 ──────────────────────────────────────────────────────────────
    def _start(self):
        if MISSING:
            self._show_missing()
            return
        if self._processing:
            return
        if not self._file_list:
            messagebox.showwarning("ファイル未登録", "PDFファイルを追加してください。")
            return

        self._processing = True
        self._run_btn.configure(state="disabled", text="処理中…", bg="#333d55")
        self._progress['value'] = 0
        self._progress['maximum'] = len(self._file_list)
        self._status.set(f"処理中… 0 / {len(self._file_list)}")
        self._clear_log()
        self._log_msg(f"処理開始: {len(self._file_list)} 件", "accent")

        thread = threading.Thread(
            target=run_batch,
            args=(
                list(self._file_list),
                lambda msg: self._log_queue.put(("info", msg)),
                lambda cur, tot: self._log_queue.put(("progress", (cur, tot))),
                lambda ok, ng: self._log_queue.put(("done", (ok, ng))),
            ),
            daemon=True
        )
        thread.start()

    # ── ログポーリング ────────────────────────────────────────────────────────
    def _poll_log(self):
        while not self._log_queue.empty():
            kind, payload = self._log_queue.get_nowait()
            if kind == "info":
                tag = ("success" if "完了" in payload or "保存" in payload
                       else "error"   if "エラー" in payload
                       else "warn"    if "警告" in payload or "スキップ" in payload
                       else "accent"  if payload.startswith("[")
                       else "info")
                self._log_msg(payload, tag)
            elif kind == "progress":
                cur, tot = payload
                self._progress['value'] = cur
                self._status.set(f"処理中… {cur} / {tot}")
            elif kind == "done":
                ok_list, ng_list = payload
                self._processing = False
                self._run_btn.configure(state="normal",
                                        text="▶  処理開始", bg=self.ACCENT)
                total = len(ok_list) + len(ng_list)
                if not ng_list:
                    self._status.set(f"✓  完了！  {len(ok_list)} 件すべて成功")
                    self._log_msg("✓  すべて正常に完了しました", "success")
                    messagebox.showinfo("完了",
                        f"{len(ok_list)} 件の処理が完了しました。\n"
                        "各PDFと同じフォルダに _linked.pdf で保存されました。")
                else:
                    self._status.set(
                        f"完了  成功 {len(ok_list)} / 失敗 {len(ng_list)} / 計 {total}")
                    self._log_msg(
                        f"✗  {len(ng_list)} 件でエラーが発生しました", "error")
                    err_detail = "\n".join(f"・{name}" for name, _ in ng_list)
                    messagebox.showwarning("一部エラー",
                        f"成功: {len(ok_list)} 件 / 失敗: {len(ng_list)} 件\n\n"
                        f"失敗したファイル:\n{err_detail}\n\n"
                        "詳細はログを確認してください。")
        self.after(100, self._poll_log)

    # ── ログ操作 ──────────────────────────────────────────────────────────────
    def _log_msg(self, msg, tag="info"):
        self._log.configure(state="normal")
        self._log.insert("end", msg + "\n", tag)
        self._log.see("end")
        self._log.configure(state="disabled")

    def _clear_log(self):
        self._log.configure(state="normal")
        self._log.delete("1.0", "end")
        self._log.configure(state="disabled")

    def _show_missing(self):
        libs = "\n".join(f"  pip install {m}" for m in MISSING)
        messagebox.showerror(
            "ライブラリ不足",
            f"以下のライブラリをインストールしてください:\n\n{libs}\n\n"
            "インストール後、アプリを再起動してください。"
        )


# ═══════════════════════════════════════════════════════════════════════════════
#  エントリポイント
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    app = App()
    app.mainloop()
