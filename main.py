import sys
import secrets
import math
import json
import base64
import re
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QTabWidget, QPushButton,
    QTextEdit, QLabel, QLineEdit, QFileDialog, QComboBox, QGroupBox, QMessageBox, QSplitter,
    QSpinBox, QMenuBar, QSlider, QProgressBar, QScrollArea, QCheckBox, QDialog
)
from PySide6.QtCore import Qt, QTimer
from PySide6.QtGui import QFont, QPalette, QColor, QAction
from cryptography.hazmat.primitives.asymmetric import rsa as crypto_rsa, padding as crypto_padding
from cryptography.hazmat.primitives import hashes, serialization

# -------------------- Константы --------------------
METHOD_MAX_BITS = {"miller-rabin": 2048, "trial": 32, "sieve": 20, "genpr": 10000}


# -------------------- Утилиты --------------------
def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    d, x1, y1 = extended_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return d, x, y


def mod_inverse(a, m):
    d, x, _ = extended_gcd(a, m)
    if d != 1:
        raise ValueError("Нет обратного элемента для данного e по модулю φ(N).")
    return x % m


def parse_numbers(s: str):
    s = re.sub(r'[\[\](){},;\s]+', ' ', s.strip())
    out = []
    for token in s.split():
        if re.fullmatch(r'[+]?\d+', token):
            out.append(int(token))
    return out


def encode_text_to_blocks(text: str, n: int):
    data = text.encode('utf-8')
    # Размер блока в байтах.
    block_bytes = max(1, (n.bit_length() - 1) // 8)

    blocks = []
    plain_lengths = []

    for i in range(0, len(data), block_bytes):
        chunk = data[i:i + block_bytes]
        blocks.append(int.from_bytes(chunk, 'big'))
        plain_lengths.append(len(chunk))
    return blocks, block_bytes, plain_lengths, len(data)


def decode_blocks_to_text_precise(blocks, block_bytes, plain_lengths=None, total_plain_bytes=None):
    raw = bytearray()
    if plain_lengths and len(plain_lengths) == len(blocks):
        for b, plen in zip(blocks, plain_lengths):
            try:
                full = b.to_bytes(block_bytes, 'big')
                raw.extend(full[-plen:])
            except OverflowError:
                actual_len = (b.bit_length() + 7) // 8
                full = b.to_bytes(actual_len, 'big')
                raw.extend(full)
    else:
        for b in blocks:
            try:
                chunk = b.to_bytes(block_bytes, 'big').lstrip(b'\x00')
            except OverflowError:
                actual_len = (b.bit_length() + 7) // 8
                chunk = b.to_bytes(actual_len, 'big').lstrip(b'\x00')
            raw.extend(chunk)

    if total_plain_bytes is not None and len(raw) > total_plain_bytes:
        raw = raw[:total_plain_bytes]
    try:
        return raw.decode('utf-8')
    except UnicodeDecodeError:
        return raw.decode('utf-8', 'replace')


def decode_blocks_to_text(blocks, block_bytes):
    raw = bytearray()
    for b in blocks:
        try:
            chunk = b.to_bytes(block_bytes, 'big').lstrip(b'\x00')
        except OverflowError:
            actual_len = (b.bit_length() + 7) // 8
            chunk = b.to_bytes(actual_len, 'big').lstrip(b'\x00')
        raw.extend(chunk)
    try:
        return raw.decode('utf-8')
    except UnicodeDecodeError:
        return raw.decode('utf-8', 'replace')


def blocks_to_compact_hex(blocks, N):
    cipher_block_bytes = (N.bit_length() + 7) // 8
    return ''.join(b.to_bytes(cipher_block_bytes, 'big').hex() for b in blocks)


def compact_hex_to_blocks(hex_str, N):
    hex_str = hex_str.strip()
    cipher_block_bytes = (N.bit_length() + 7) // 8
    one_len = cipher_block_bytes * 2
    if len(hex_str) % one_len != 0:
        raise ValueError("Длина компактной HEX-строки не кратна размеру блока.")
    blocks = []
    for i in range(0, len(hex_str), one_len):
        chunk_hex = hex_str[i:i + one_len]
        if not re.fullmatch(r'[0-9a-fA-F]+', chunk_hex):
            raise ValueError("Строка содержит не HEX символы.")
        val = int.from_bytes(bytes.fromhex(chunk_hex), 'big')
        if val >= N:
            raise ValueError("Блок >= N (некорректные данные).")
        blocks.append(val)
    return blocks


def byte_to_char_repr(b: int) -> str:
    return chr(b) if 32 <= b <= 126 else '.'


def bytes_to_printable_utf8(block: bytes) -> str:
    # Используем errors='replace', чтобы вместо ошибок декодирования
    # (когда буква разорвана между блоками) ставился знак , а не кракозябры.
    return block.decode('utf-8', errors='replace')


# -------------------- Генераторы --------------------
class LCG:
    def __init__(self, seed, a=1664525, b=1013904223, m=2 ** 32):
        self.state = seed % m
        self.a = a
        self.b = b
        self.m = m

    def next(self):
        self.state = (self.a * self.state + self.b) % self.m
        return self.state

    def get_formula_info(self):
        return f"Y_i = ({self.a} • {self.state} + {self.b}) mod {self.m}"

    def get_params_description(self):
        return (f"Пояснение: a={self.a} (множитель), b={self.b} (приращение), "
                f"m={self.m} (модуль), Y_i-1={self.state} (пред. число)")


class Multiplicative:
    def __init__(self, seed, a=16807, m=2 ** 31 - 1):
        self.state = seed % m
        self.a = a
        self.m = m

    def next(self):
        self.state = (self.a * self.state) % self.m
        return self.state

    def get_formula_info(self):
        return f"Y_i = ({self.a} • {self.state}) mod {self.m}"

    def get_params_description(self):
        return (f"Пояснение: a={self.a} (множитель), m={self.m} (модуль), "
                f"Y_i-1={self.state} (пред. число). Приращение b=0.")


class Additive:
    def __init__(self, seed1, seed2=None, m=2 ** 32):
        self.x = seed1 % m
        self.y = (seed2 or (seed1 * 1103515245 + 12345)) % m
        self.m = m

    def next(self):
        z = (self.x + self.y) % self.m
        self.x, self.y = self.y, z
        return z

    def get_formula_info(self):
        return f"Y_i = ({self.x} + {self.y}) mod {self.m}"

    def get_params_description(self):
        return (f"Пояснение: m={self.m} (модуль), Y_i-1={self.x} (пред. число), "
                f"Y_i-2={self.y} (пред-пред. число). Множителя нет.")


# -------------------- Простые числа --------------------
_SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
for n in range(101, 1000, 2):
    if all(n % p for p in _SMALL_PRIMES if p * p <= n):
        _SMALL_PRIMES.append(n)


def is_prime_deterministic(n):
    if n < 2: return False
    for p in _SMALL_PRIMES:
        if n % p == 0: return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in [2, 325, 9375, 28178, 450775, 9780504, 1795265022]:
        if a % n == 0: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1: break
        else:
            return False
    return True


def is_prime_miller_rabin(n, k=10):
    if n < 2: return False
    for p in _SMALL_PRIMES[:15]:
        if n % p == 0: return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for _ in range(k):
        a = secrets.randbelow(n - 3) + 2
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for __ in range(s - 1):
            x = (x * x) % n
            if x == n - 1: break
        else:
            return False
    return True


def genpr_algorithm(m, k):
    if m < 3: m = 3
    if m % 2 == 0: m += 1
    n = m + 2 * k - 2
    A = [1] * k
    d = 3
    while True:
        if d * d > n:
            break
        inv_2 = (d + 1) // 2
        start_j = ((-m * inv_2) % d)
        if (m + 2 * start_j) == d:
            start_j += d
        current_j = start_j
        while current_j < k:
            A[current_j] = 0
            current_j += d
        if d % 6 == 1:
            d += 4
        else:
            d += 2
    primes = []
    for i in range(k):
        if A[i] == 1:
            primes.append(m + 2 * i)
    return [p for p in primes if is_prime_deterministic(p)]


def generate_large_prime(bits=None, method='miller-rabin', genpr_params=None):
    if method == 'genpr':
        if not genpr_params:
            m_val = 1 << (bits - 1) if bits else 1001
            k_val = 1000
        else:
            m_val, k_val = genpr_params
        primes = genpr_algorithm(m_val, k_val)
        if primes:
            return secrets.choice(primes)
        else:
            raise ValueError(f"GENPR: нет простых чисел в диапазоне [{m_val}, {m_val + 2 * k_val - 2}]")

    if bits < 2: raise ValueError("Битность ≥ 2")
    max_allowed = METHOD_MAX_BITS.get(method, 1024)
    if bits > max_allowed:
        raise ValueError(f"Метод '{method}' поддерживает ≤ {max_allowed} бит.")

    while True:
        candidate = secrets.randbits(bits)
        candidate |= (1 << (bits - 1)) | 1
        if any(candidate % p == 0 and candidate != p for p in _SMALL_PRIMES):
            continue
        if method == 'trial':
            if candidate < 2: continue
            limit = int(math.isqrt(candidate))
            f = 3
            while f <= limit and candidate % f: f += 2
            if f > limit: return candidate
        elif method == 'sieve':
            limit = (1 << bits) - 1
            sieve = [True] * (limit + 1);
            sieve[0:2] = [False, False]
            for i in range(2, int(limit ** 0.5) + 1):
                if sieve[i]: sieve[i * i::i] = [False] * ((limit - i * i) // i + 1)
            primes = [i for i, fl in enumerate(sieve) if fl]
            if primes: return secrets.choice(primes)
        elif method == 'miller-rabin':
            if is_prime_miller_rabin(candidate, k=10): return candidate


def mod_exp(base, exp, mod):
    return pow(base, exp, mod)


# -------------------- Окно просмотра Гаммы --------------------
class GammaDisplayWindow(QDialog):
    def __init__(self, gamma_bytes, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Просмотр Гаммы")
        self.resize(600, 500)
        layout = QVBoxLayout(self)

        layout.addWidget(QLabel("<b>16-ричный вид (HEX):</b>"))
        self.hex_view = QTextEdit()
        self.hex_view.setReadOnly(True)
        hex_str = gamma_bytes.hex(" ").upper()
        self.hex_view.setPlainText(hex_str)
        layout.addWidget(self.hex_view)

        layout.addWidget(QLabel("<b>Десятичный вид (0-255):</b>"))
        self.dec_view = QTextEdit()
        self.dec_view.setReadOnly(True)
        dec_str = ", ".join(str(b) for b in gamma_bytes)
        self.dec_view.setPlainText(dec_str)
        layout.addWidget(self.dec_view)

        btn_close = QPushButton("Закрыть")
        btn_close.clicked.connect(self.close)
        layout.addWidget(btn_close)


# -------------------- GammaTab --------------------
class GammaTab(QWidget):
    MAX_LOG_BLOCKS = 1000

    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)

        self.last_gamma = b""

        top_bar = QHBoxLayout()
        self.btn_load = QPushButton("📂 Загрузить файл (.txt)")
        self.btn_load.clicked.connect(self.load_file)
        top_bar.addWidget(self.btn_load)
        top_bar.addStretch()
        layout.addLayout(top_bar)

        splitter = QSplitter(Qt.Horizontal)
        layout.addWidget(splitter)

        left_group = QGroupBox("Исходные данные")
        left_layout = QVBoxLayout(left_group)
        self.input_text = QTextEdit()
        self.input_text.setPlaceholderText("Введите текст...")
        left_layout.addWidget(self.input_text)
        splitter.addWidget(left_group)

        right_group = QGroupBox("Результат")
        right_layout = QVBoxLayout(right_group)
        self.output_text = QTextEdit()
        self.output_text.setReadOnly(True)
        right_layout.addWidget(self.output_text)

        self.btn_show_gamma = QPushButton("👁 Показать гамму (HEX/DEC)")
        self.btn_show_gamma.clicked.connect(self.show_gamma_window)
        self.btn_show_gamma.setEnabled(False)
        right_layout.addWidget(self.btn_show_gamma)

        splitter.addWidget(right_group)

        params_group = QGroupBox("Параметры генератора (a, b, m)")
        params_layout = QVBoxLayout()

        seed_layout = QHBoxLayout()
        seed_layout.addWidget(QLabel("Seed (Y0):"))
        self.seed_input = QLineEdit("12345")
        self.bits_combo = QComboBox()
        self.bits_combo.addItems(["32", "64", "128", "256"])
        self.bits_combo.setCurrentText("128")
        self.btn_gen_seed = QPushButton("🎲 Rand Seed")
        self.btn_gen_seed.clicked.connect(self.generate_seed)
        seed_layout.addWidget(self.seed_input)
        seed_layout.addWidget(self.bits_combo)
        seed_layout.addWidget(self.btn_gen_seed)
        params_layout.addLayout(seed_layout)

        gen_row = QHBoxLayout()
        gen_row.addWidget(QLabel("Тип:"))
        self.gen_combo = QComboBox()
        self.gen_combo.addItems(["LCG (Линейный)", "Мультипликативный", "Аддитивный"])
        self.gen_combo.currentIndexChanged.connect(self.on_gen_changed)
        gen_row.addWidget(self.gen_combo)
        params_layout.addLayout(gen_row)

        coeffs_row = QHBoxLayout()
        self.a_label = QLabel("a:")
        self.a_input = QLineEdit("1664525")
        self.b_label = QLabel("b:")
        self.b_input = QLineEdit("1013904223")
        self.m_label = QLabel("m:")
        self.m_input = QLineEdit("4294967296")
        coeffs_row.addWidget(self.a_label)
        coeffs_row.addWidget(self.a_input)
        coeffs_row.addWidget(self.b_label)
        coeffs_row.addWidget(self.b_input)
        coeffs_row.addWidget(self.m_label)
        coeffs_row.addWidget(self.m_input)
        params_layout.addLayout(coeffs_row)

        key_btns = QHBoxLayout()
        self.btn_save_key = QPushButton("💾 Сохр. ключи")
        self.btn_save_key.clicked.connect(self.save_key_file)
        self.btn_load_key = QPushButton("📥 Загр. ключи")
        self.btn_load_key.clicked.connect(self.load_key_file)
        key_btns.addWidget(self.btn_save_key)
        key_btns.addWidget(self.btn_load_key)
        key_btns.addStretch()
        params_layout.addLayout(key_btns)

        params_group.setLayout(params_layout)
        layout.addWidget(params_group)

        act_row = QHBoxLayout()
        self.btn_encrypt = QPushButton("🔒 Шифровать")
        self.btn_encrypt.clicked.connect(self.encrypt)
        self.btn_decrypt = QPushButton("🔓 Дешифровать")
        self.btn_decrypt.clicked.connect(self.decrypt)
        act_row.addWidget(self.btn_encrypt)
        act_row.addWidget(self.btn_decrypt)
        layout.addLayout(act_row)

        self.btn_save = QPushButton("💾 Сохранить результат")
        self.btn_save.clicked.connect(self.save_result)
        layout.addWidget(self.btn_save)

        anim_group = QGroupBox("Анимация")
        anim_layout = QVBoxLayout(anim_group)
        controls_row = QHBoxLayout()
        self.btn_anim_encrypt = QPushButton("▶ Шифр.")
        self.btn_anim_decrypt = QPushButton("▶ Дешифр.")
        self.btn_anim_pause = QPushButton("⏸")
        self.btn_anim_step = QPushButton("⏭")
        self.btn_anim_stop = QPushButton("⏹")
        for b in (self.btn_anim_pause, self.btn_anim_step, self.btn_anim_stop):
            b.setEnabled(False)
        self.btn_anim_encrypt.clicked.connect(lambda: self.start_animation('encrypt'))
        self.btn_anim_decrypt.clicked.connect(lambda: self.start_animation('decrypt'))
        self.btn_anim_pause.clicked.connect(self.toggle_pause)
        self.btn_anim_step.clicked.connect(self.animation_step_manual)
        self.btn_anim_stop.clicked.connect(self.stop_animation)

        controls_row.addWidget(self.btn_anim_encrypt)
        controls_row.addWidget(self.btn_anim_decrypt)
        controls_row.addWidget(self.btn_anim_pause)
        controls_row.addWidget(self.btn_anim_step)
        controls_row.addWidget(self.btn_anim_stop)
        anim_layout.addLayout(controls_row)

        speed_row = QHBoxLayout()
        speed_row.addWidget(QLabel("Скор:"))
        self.speed_slider = QSlider(Qt.Horizontal)
        self.speed_slider.setRange(1, 10)
        self.speed_slider.setValue(5)
        self.speed_slider.valueChanged.connect(self.update_timer_interval)
        speed_row.addWidget(self.speed_slider)
        self.progress = QProgressBar()
        self.progress.setMinimum(0)
        speed_row.addWidget(self.progress)
        self.current_block_label = QLabel("Блок: 0")
        speed_row.addWidget(self.current_block_label)
        anim_layout.addLayout(speed_row)
        layout.addWidget(anim_group)

        log_group = QGroupBox("Лог (Детализация)")
        log_layout = QVBoxLayout(log_group)
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        font = QFont("Consolas", 9)
        if not font.exactMatch(): font = QFont("Courier New", 9)
        self.log_text.setFont(font)
        log_layout.addWidget(self.log_text)

        log_btns = QHBoxLayout()
        self.btn_clear_log = QPushButton("🗑 Очистить")
        self.btn_clear_log.clicked.connect(self.log_text.clear)
        self.btn_save_log = QPushButton("💾 Сохранить лог")
        self.btn_save_log.clicked.connect(self.save_log)

        log_btns.addWidget(self.btn_clear_log)
        log_btns.addWidget(self.btn_save_log)
        log_layout.addLayout(log_btns)
        layout.addWidget(log_group)

        self.animation_timer = QTimer(self)
        self.animation_timer.timeout.connect(self.animation_step)
        self.animation_running = False
        self.animation_paused = False
        self.animation_mode = None
        self.animation_data = None
        self.animation_gen = None
        self.animation_index = 0
        self.animation_total = 0
        self.animation_output = bytearray()
        self.animation_full_gamma = bytearray()

        self.on_gen_changed(0)

    def on_gen_changed(self, index):
        if index == 0:
            self.a_input.setEnabled(True);
            self.a_label.setText("a:")
            self.b_input.setEnabled(True);
            self.b_input.setText("1013904223")
            self.m_input.setEnabled(True)
        elif index == 1:
            self.a_input.setEnabled(True);
            self.a_label.setText("a:")
            self.b_input.setEnabled(False);
            self.b_input.setText("0")
            self.m_input.setEnabled(True)
        elif index == 2:
            self.a_input.setEnabled(False);
            self.a_label.setText("a (N/A):")
            self.b_input.setEnabled(False);
            self.b_input.setText("N/A")
            self.m_input.setEnabled(True)

    def get_generator(self):
        try:
            seed = int(self.seed_input.text())
            m_val = int(self.m_input.text())
            idx = self.gen_combo.currentIndex()
            if idx == 0:
                a_val = int(self.a_input.text())
                b_val = int(self.b_input.text())
                return LCG(seed, a=a_val, b=b_val, m=m_val)
            elif idx == 1:
                a_val = int(self.a_input.text())
                return Multiplicative(seed, a=a_val, m=m_val)
            else:
                return Additive(seed, m=m_val)
        except ValueError:
            QMessageBox.warning(self, "Ошибка", "Проверьте, что a, b, m и seed - целые числа.")
            return LCG(12345)

    def load_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Открыть", "", "TXT (*.txt);;All (*)")
        if path:
            with open(path, 'r', encoding='utf-8') as f: self.input_text.setPlainText(f.read())

    def generate_seed(self):
        try:
            bits = int(self.bits_combo.currentText())
            self.seed_input.setText(str(secrets.randbits(bits)))
        except:
            pass

    def save_key_file(self):
        try:
            seed = self.seed_input.text()
            gen_idx = self.gen_combo.currentIndex()
            a = self.a_input.text()
            b = self.b_input.text()
            m = self.m_input.text()
            content = (f"seed={seed}\ntype={gen_idx}\na={a}\nb={b}\nm={m}\n")
            path, _ = QFileDialog.getSaveFileName(self, "Сохранить ключ", "", "TXT (*.txt)")
            if path:
                with open(path, 'w', encoding='utf-8') as f: f.write(content)
                QMessageBox.information(self, "OK", "Сохранено")
        except Exception as e:
            QMessageBox.critical(self, "ERR", str(e))

    def load_key_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Загрузить ключ", "", "TXT (*.txt)")
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            for line in lines:
                if '=' not in line: continue
                k, v = line.strip().split('=', 1)
                if k == 'seed':
                    self.seed_input.setText(v)
                elif k == 'type':
                    self.gen_combo.setCurrentIndex(int(v))
                elif k == 'a':
                    self.a_input.setText(v)
                elif k == 'b':
                    self.b_input.setText(v)
                elif k == 'm':
                    self.m_input.setText(v)
            self.on_gen_changed(self.gen_combo.currentIndex())
        except Exception as e:
            QMessageBox.critical(self, "ERR", str(e))

    def process_gamma(self, data_bytes, gen):
        block_size = 8
        for i in range(0, len(data_bytes), block_size):
            block = data_bytes[i:i + block_size]
            formula_str = gen.get_formula_info()
            params_desc = gen.get_params_description()

            raw_val = gen.next()
            full_info = f"{formula_str} = {raw_val}\n    {params_desc}"

            gamma = bytearray()
            gamma.append(raw_val & 0xFF)
            for _ in range(len(block) - 1):
                gamma.append(gen.next() & 0xFF)

            out_block = bytes(b ^ g for b, g in zip(block, gamma))
            yield i // block_size, block, gamma, out_block, full_info

    def encrypt(self):
        text = self.input_text.toPlainText()
        if not text: return
        gen = self.get_generator()
        data = text.encode('utf-8')
        out = bytearray()
        full_log = []
        self.last_gamma = bytearray()

        for idx, inp, gam, res, info in self.process_gamma(data, gen):
            out.extend(res)
            self.last_gamma.extend(gam)

            inp_chars = bytes_to_printable_utf8(inp)
            res_chars = bytes_to_printable_utf8(res)

            log_entry = (
                f"Block {idx}:\n"
                f"  Info:  {info}\n"
                f"  Text:  '{inp_chars}'\n"
                f"  InHex: {inp.hex()}\n"
                f"  Gamma: {gam.hex()}\n"
                f"  Out:   {res.hex()} (Encrypted: '{res_chars}')"
            )
            full_log.append(log_entry)

        self.output_text.setPlainText(out.hex())
        self.log_text.setPlainText('\n---------------------------------\n'.join(full_log))
        self.btn_show_gamma.setEnabled(True)

    def decrypt(self):
        src = self.input_text.toPlainText().strip()
        if not src: return
        try:
            data = bytes.fromhex(src)
        except:
            data = src.encode('utf-8')
        gen = self.get_generator()
        out = bytearray()
        full_log = []
        self.last_gamma = bytearray()

        for idx, inp, gam, res, info in self.process_gamma(data, gen):
            out.extend(res)
            self.last_gamma.extend(gam)

            inp_chars = bytes_to_printable_utf8(inp)
            res_chars = bytes_to_printable_utf8(res)

            log_entry = (
                f"Block {idx}:\n"
                f"  Info:  {info}\n"
                f"  InHex: {inp.hex()}\n"
                f"  Gamma: {gam.hex()}\n"
                f"  Out:   {res.hex()}\n"
                f"  Text:  '{res_chars}'"
            )
            full_log.append(log_entry)

        try:
            res_txt = out.decode('utf-8')
        except:
            res_txt = out.decode('utf-8', 'replace')

        self.output_text.setPlainText(res_txt)
        self.log_text.setPlainText('\n---------------------------------\n'.join(full_log))
        self.btn_show_gamma.setEnabled(True)

    def show_gamma_window(self):
        if not self.last_gamma:
            QMessageBox.information(self, "Информация", "Сначала выполните шифрование или дешифрование.")
            return
        dialog = GammaDisplayWindow(self.last_gamma, self)
        dialog.exec()

    def save_result(self):
        txt = self.output_text.toPlainText()
        if not txt: QMessageBox.warning(self, "", "Пусто"); return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить результат", "", "Text Files (*.txt)")
        if path:
            with open(path, 'w', encoding='utf-8') as f: f.write(txt)
            QMessageBox.information(self, "OK", "Сохранено")

    def save_log(self):
        txt = self.log_text.toPlainText()
        if not txt: QMessageBox.warning(self, "Пусто", "Лог пуст, нечего сохранять."); return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить лог", "", "Text Files (*.txt)")
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(txt)
                QMessageBox.information(self, "OK", "Лог сохранен")
            except Exception as e:
                QMessageBox.critical(self, "Ошибка", str(e))

    def update_timer_interval(self):
        self.animation_timer.setInterval(1100 - self.speed_slider.value() * 100)

    def start_animation(self, mode):
        if self.animation_running: return
        txt = self.input_text.toPlainText().strip()
        if not txt: return
        try:
            if mode == 'decrypt':
                try:
                    self.animation_data = bytes.fromhex(txt)
                except:
                    self.animation_data = txt.encode('utf-8')
            else:
                self.animation_data = txt.encode('utf-8')

            self.animation_gen = self.get_generator()
            self.animation_mode = mode
            self.animation_index = 0
            self.animation_total = math.ceil(len(self.animation_data) / 8)
            self.animation_output = bytearray()
            self.animation_full_gamma = bytearray()

            self.log_text.clear()
            self.output_text.clear()

            self.progress.setMaximum(self.animation_total)
            self.progress.setValue(0)
            self.animation_running = True
            self.animation_paused = False
            self.btn_show_gamma.setEnabled(False)

            self.btn_anim_pause.setEnabled(True)
            self.btn_anim_step.setEnabled(True)
            self.btn_anim_stop.setEnabled(True)
            self.btn_anim_encrypt.setEnabled(False)
            self.btn_anim_decrypt.setEnabled(False)

            self.update_timer_interval()
            self.animation_timer.start()
        except Exception as e:
            QMessageBox.critical(self, "Err", str(e))

    def animation_step(self):
        if self.animation_running and not self.animation_paused: self._do_step()

    def animation_step_manual(self):
        if self.animation_running:
            self.animation_timer.stop();
            self.animation_paused = True;
            self._do_step()

    def toggle_pause(self):
        if not self.animation_running: return
        self.animation_paused = not self.animation_paused
        if self.animation_paused:
            self.animation_timer.stop()
        else:
            self.animation_timer.start()

    def stop_animation(self):
        self.animation_running = False
        self.animation_timer.stop()
        self.btn_anim_pause.setEnabled(False)
        self.btn_anim_step.setEnabled(False)
        self.btn_anim_stop.setEnabled(False)
        self.btn_anim_encrypt.setEnabled(True)
        self.btn_anim_decrypt.setEnabled(True)
        self.last_gamma = self.animation_full_gamma
        self.btn_show_gamma.setEnabled(True)

    def _do_step(self):
        if self.animation_index >= self.animation_total:
            self.stop_animation();
            return

        start = self.animation_index * 8
        block = self.animation_data[start:start + 8]
        gen = self.animation_gen

        info = f"{gen.get_formula_info()} = {gen.next()}\n    {gen.get_params_description()}"

        gamma = bytearray([gen.state & 0xFF])
        for _ in range(len(block) - 1):
            gamma.append(gen.next() & 0xFF)

        out = bytes(b ^ g for b, g in zip(block, gamma))

        self.animation_output.extend(out)
        self.animation_full_gamma.extend(gamma)

        inp_chars = bytes_to_printable_utf8(block)
        out_chars = bytes_to_printable_utf8(out)

        log_entry = (
            f"Block {self.animation_index}:\n"
            f"  Info:  {info}\n"
            f"  Text:  '{inp_chars}'\n"
            f"  InHex: {block.hex()}\n"
            f"  Gamma: {gamma.hex()}\n"
            f"  Out:   {out.hex()} -> '{out_chars}'"
        )
        self.log_text.append(log_entry + "\n-----------------")

        if self.animation_mode == 'encrypt':
            self.output_text.setPlainText(self.animation_output.hex())
        else:
            self.output_text.setPlainText(bytes_to_printable_utf8(self.animation_output))

        self.animation_index += 1
        self.progress.setValue(self.animation_index)
        self.current_block_label.setText(f"Блок: {self.animation_index}")

        if self.animation_index >= self.animation_total: self.stop_animation()


# -------------------- ModArithmeticTab --------------------
class ModArithmeticTab(QWidget):
    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)
        params_group = QGroupBox("Генерация двух простых чисел");
        params_layout = QHBoxLayout()
        self.bits_label = QLabel("Битность:")
        params_layout.addWidget(self.bits_label)
        self.bits_spin = QSpinBox();
        self.bits_spin.setRange(8, 2048);
        self.bits_spin.setValue(128)
        params_layout.addWidget(self.bits_spin)
        self.genpr_m_label = QLabel("m (GENPR):")
        self.genpr_m_spin = QSpinBox();
        self.genpr_m_spin.setRange(3, 999999999);
        self.genpr_m_spin.setValue(1001)
        self.genpr_k_label = QLabel("k (GENPR):")
        self.genpr_k_spin = QSpinBox();
        self.genpr_k_spin.setRange(1, 999999);
        self.genpr_k_spin.setValue(100)
        self.genpr_m_label.setVisible(False);
        self.genpr_m_spin.setVisible(False)
        self.genpr_k_label.setVisible(False);
        self.genpr_k_spin.setVisible(False)
        params_layout.addWidget(self.genpr_m_label);
        params_layout.addWidget(self.genpr_m_spin)
        params_layout.addWidget(self.genpr_k_label);
        params_layout.addWidget(self.genpr_k_spin)
        params_layout.addWidget(QLabel("Метод:"))
        self.method_combo = QComboBox()
        self.method_combo.addItems(
            ["Миллер–Рабин (рекомендуется)", "Перебор (до 32 бит)", "Решето Эратосфена (до 20 бит)",
             "GENPR (Generate Primes)"])
        self.method_combo.currentIndexChanged.connect(self.on_method_changed)
        params_layout.addWidget(self.method_combo)
        self.btn_gen = QPushButton("🎲 Сгенерировать 2 простых");
        self.btn_gen.clicked.connect(self.generate_primes);
        params_layout.addWidget(self.btn_gen)
        params_group.setLayout(params_layout);
        layout.addWidget(params_group)
        primes_layout = QHBoxLayout()
        self.p1_edit = QLineEdit();
        self.p1_edit.setPlaceholderText("p1")
        self.p2_edit = QLineEdit();
        self.p2_edit.setPlaceholderText("p2")
        primes_layout.addWidget(self.p1_edit);
        primes_layout.addWidget(self.p2_edit);
        layout.addLayout(primes_layout)
        ops_group = QGroupBox("Операции: a, b, n, m");
        ops_layout = QVBoxLayout()
        r1 = QHBoxLayout();
        r1.addWidget(QLabel("a ="));
        self.a_edit = QLineEdit();
        r1.addWidget(self.a_edit);
        r1.addWidget(QLabel("b ="));
        self.b_edit = QLineEdit();
        r1.addWidget(self.b_edit);
        ops_layout.addLayout(r1)
        r2 = QHBoxLayout();
        r2.addWidget(QLabel("n ="));
        self.n_edit = QLineEdit("17");
        r2.addWidget(self.n_edit);
        r2.addWidget(QLabel("m ="));
        self.m_edit = QLineEdit("101");
        r2.addWidget(self.m_edit);
        ops_layout.addLayout(r2)
        ops_group.setLayout(ops_layout);
        layout.addWidget(ops_group)
        btns_layout = QHBoxLayout()
        self.btn_use = QPushButton("→ Использовать p1,p2 как a,b");
        self.btn_use.clicked.connect(self.use_primes)
        self.btn_calc = QPushButton("🔢 Выполнить операции");
        self.btn_calc.clicked.connect(self.calculate_all)
        btns_layout.addWidget(self.btn_use);
        btns_layout.addWidget(self.btn_calc);
        btns_layout.addStretch();
        layout.addLayout(btns_layout)
        self.results = QTextEdit();
        self.results.setReadOnly(True);
        self.results.setPlaceholderText("Результаты...");
        layout.addWidget(self.results)

    def on_method_changed(self):
        method = self.get_method()
        is_genpr = (method == "genpr")
        self.bits_label.setVisible(not is_genpr)
        self.bits_spin.setVisible(not is_genpr)
        self.genpr_m_label.setVisible(is_genpr)
        self.genpr_m_spin.setVisible(is_genpr)
        self.genpr_k_label.setVisible(is_genpr)
        self.genpr_k_spin.setVisible(is_genpr)
        if not is_genpr:
            self.adjust_bits_limit()

    def adjust_bits_limit(self):
        method = self.get_method()
        max_bits = METHOD_MAX_BITS.get(method, 1024)
        if self.bits_spin.value() > max_bits:
            self.bits_spin.setValue(max_bits)
            QMessageBox.information(self, "ℹ️ Ограничение", f"Для '{method}' максимум {max_bits} бит.")
        self.bits_spin.setMaximum(max_bits)

    def get_method(self):
        t = self.method_combo.currentText()
        if "Миллер" in t: return "miller-rabin"
        if "Перебор" in t: return "trial"
        if "Решето" in t: return "sieve"
        if "GENPR" in t: return "genpr"
        return "miller-rabin"

    def generate_primes(self):
        try:
            method = self.get_method()
            bits = self.bits_spin.value()
            genpr_params = None
            if method == 'genpr':
                m = self.genpr_m_spin.value()
                k = self.genpr_k_spin.value()
                if m % 2 == 0: m += 1
                genpr_params = (m, k)
            p1 = generate_large_prime(bits, method, genpr_params)
            p2 = generate_large_prime(bits, method, genpr_params)
            attempts = 0
            while p1 == p2 and attempts < 10:
                p2 = generate_large_prime(bits, method, genpr_params)
                attempts += 1
            self.p1_edit.setText(str(p1));
            self.p2_edit.setText(str(p2))
            QMessageBox.information(self, "✅ Успех", f"Сгенерированы два простых (Метод: {method}).")
        except Exception as e:
            QMessageBox.critical(self, "❌ Генерация", str(e))

    def use_primes(self):
        try:
            p1 = self.p1_edit.text();
            p2 = self.p2_edit.text()
            if not p1 or not p2: raise ValueError("Сначала сгенерируйте простые.")
            self.a_edit.setText(p1);
            self.b_edit.setText(p2)
        except Exception as e:
            QMessageBox.warning(self, "⚠️ Ошибка", str(e))

    def calculate_all(self):
        try:
            a_txt = self.a_edit.text().strip()
            b_txt = self.b_edit.text().strip()
            n_txt = self.n_edit.text().strip()
            m_txt = self.m_edit.text().strip()
            if not (a_txt and b_txt and n_txt and m_txt): raise ValueError("Заполните a, b, n, m.")
            a = int(a_txt);
            b = int(b_txt);
            n = int(n_txt);
            m = int(m_txt)
            if b == 0: raise ValueError("b не может быть 0.")
            if m == 0: raise ValueError("m не может быть 0.")
            add = a + b;
            sub = a - b;
            mul = a * b;
            div_floor = a // b;
            modv_ab = a % b
            try:
                div_float = a / b
                if abs(div_float) > 1e300:
                    div_str = "слишком большое"
                else:
                    div_str = f"{div_float:.20g}"
                    if '.' not in div_str and 'e' not in div_str: div_str += ".0"
            except Exception:
                div_str = "ошибка"
            amodm = a % m
            pow_full = pow(a, n)
            digits = len(str(pow_full))
            if digits <= 5000:
                pow_full_str = str(pow_full);
                pow_full_info = ""
            else:
                pow_full_str = f"[число слишком длинное: {digits} цифр]";
                pow_full_info = f"Длина a^n = {digits} цифр"
            pow_mod = mod_exp(a, n, m)
            lines = [
                "Операции:",
                f"a = {a}",
                f"b = {b}",
                f"n = {n}",
                f"m = {m}",
                f"a + b = {add}",
                f"a - b = {sub}",
                f"a * b = {mul}",
                f"a // b = {div_floor}",
                f"a / b = {div_str}",
                f"a mod b = {modv_ab}",
                f"a mod m = {amodm}",
                f"a^n = {pow_full_str}",
                *([pow_full_info] if pow_full_info else []),
                f"a^n mod m = {pow_mod}"
            ]
            self.results.setPlainText('\n'.join(lines))
        except Exception as e:
            QMessageBox.critical(self, "❌ Вычисления", str(e))


# -------------------- RSATab --------------------
class RSATab(QWidget):
    def __init__(self):
        super().__init__()
        main_layout = QVBoxLayout(self)
        self.scroll_area = QScrollArea();
        self.scroll_area.setWidgetResizable(True)
        container = QWidget();
        outer = QVBoxLayout(container)

        gen_group = QGroupBox("1. Генерация двух простых чисел p и q");
        gen_layout = QVBoxLayout()
        method_row = QHBoxLayout()
        method_row.addWidget(QLabel("Способ генерации:"))
        self.gen_method_combo = QComboBox()
        self.gen_method_combo.addItems(["Автом. (одинаково)", "Автом. (раздельно)", "Ручной ввод"])
        self.gen_method_combo.currentIndexChanged.connect(self.on_generation_method_changed)
        method_row.addWidget(self.gen_method_combo);
        method_row.addStretch()
        gen_layout.addLayout(method_row)

        params_row = QHBoxLayout()
        self.bits_p_label = QLabel("Битность p:");
        params_row.addWidget(self.bits_p_label)
        self.bits_p_spin = QSpinBox();
        self.bits_p_spin.setRange(32, 2048);  # Увеличили минимальное значение
        self.bits_p_spin.setValue(128);  # Увеличили дефолтное значение
        params_row.addWidget(self.bits_p_spin)

        self.genpr_m_p_label = QLabel("m (p):");
        self.genpr_m_p_spin = QSpinBox();
        self.genpr_m_p_spin.setRange(3, 10 ** 9);
        self.genpr_m_p_spin.setValue(1001)
        self.genpr_k_p_label = QLabel("k (p):");
        self.genpr_k_p_spin = QSpinBox();
        self.genpr_k_p_spin.setRange(1, 10 ** 6);
        self.genpr_k_p_spin.setValue(100)
        params_row.addWidget(self.genpr_m_p_label);
        params_row.addWidget(self.genpr_m_p_spin)
        params_row.addWidget(self.genpr_k_p_label);
        params_row.addWidget(self.genpr_k_p_spin)
        for w in [self.genpr_m_p_label, self.genpr_m_p_spin, self.genpr_k_p_label, self.genpr_k_p_spin]: w.setVisible(
            False)

        self.method_p_label = QLabel("Метод p:");
        params_row.addWidget(self.method_p_label)
        self.method_p_combo = QComboBox();
        self.method_p_combo.addItems(["Авто", "Миллер–Рабин", "Перебор", "Решето", "GENPR"])
        self.method_p_combo.currentIndexChanged.connect(self.update_p_method_ui)
        params_row.addWidget(self.method_p_combo)

        self.bits_q_label = QLabel("Битность q:");
        params_row.addWidget(self.bits_q_label)
        self.bits_q_spin = QSpinBox();
        self.bits_q_spin.setRange(32, 2048);  # Увеличили минимальное значение
        self.bits_q_spin.setValue(128);  # Увеличили дефолтное значение
        params_row.addWidget(self.bits_q_spin)

        self.genpr_m_q_label = QLabel("m (q):");
        self.genpr_m_q_spin = QSpinBox();
        self.genpr_m_q_spin.setRange(3, 10 ** 9);
        self.genpr_m_q_spin.setValue(2001)
        self.genpr_k_q_label = QLabel("k (q):");
        self.genpr_k_q_spin = QSpinBox();
        self.genpr_k_q_spin.setRange(1, 10 ** 6);
        self.genpr_k_q_spin.setValue(100)
        params_row.addWidget(self.genpr_m_q_label);
        params_row.addWidget(self.genpr_m_q_spin)
        params_row.addWidget(self.genpr_k_q_label);
        params_row.addWidget(self.genpr_k_q_spin)
        for w in [self.genpr_m_q_label, self.genpr_m_q_spin, self.genpr_k_q_label, self.genpr_k_q_spin]: w.setVisible(
            False)

        self.method_q_label = QLabel("Метод q:");
        params_row.addWidget(self.method_q_label)
        self.method_q_combo = QComboBox();
        self.method_q_combo.addItems(["Авто", "Миллер–Рабин", "Перебор", "Решето", "GENPR"])
        self.method_q_combo.currentIndexChanged.connect(self.update_q_method_ui)
        params_row.addWidget(self.method_q_combo)

        params_row.addStretch()
        self.btn_gen_pq = QPushButton("🎲 Сгенерировать p,q");
        self.btn_gen_pq.clicked.connect(self.generate_pq);
        params_row.addWidget(self.btn_gen_pq)
        gen_layout.addLayout(params_row)

        pq_row = QHBoxLayout()
        pq_row.addWidget(QLabel("p:"));
        self.p_edit = QLineEdit();
        pq_row.addWidget(self.p_edit)
        pq_row.addWidget(QLabel("q:"));
        self.q_edit = QLineEdit();
        pq_row.addWidget(self.q_edit)
        gen_layout.addLayout(pq_row)
        gen_group.setLayout(gen_layout);
        outer.addWidget(gen_group)

        key_group = QGroupBox("2. Ключи RSA");
        key_layout = QVBoxLayout()
        mode_row = QHBoxLayout()
        mode_row.addWidget(QLabel("Режим:"))
        self.key_mode_combo = QComboBox();
        self.key_mode_combo.addItems(["Рассчитать из p и q", "Ввести вручную"])
        self.key_mode_combo.currentIndexChanged.connect(self.on_key_mode_changed)
        mode_row.addWidget(self.key_mode_combo);
        mode_row.addStretch()
        key_layout.addLayout(mode_row)

        calc_row = QHBoxLayout();
        calc_row.addWidget(QLabel("e:"));
        self.e_edit = QLineEdit("65537")

        self.auto_e_cb = QCheckBox("Авто")
        self.auto_e_cb.setChecked(True)
        self.e_edit.setEnabled(False)
        self.auto_e_cb.toggled.connect(lambda checked: self.e_edit.setEnabled(not checked))

        self.btn_calc_keys = QPushButton("🔑 Рассчитать ключи");
        self.btn_calc_keys.clicked.connect(self.calculate_keys)
        calc_row.addWidget(self.e_edit);
        calc_row.addWidget(self.auto_e_cb)
        calc_row.addWidget(self.btn_calc_keys);
        calc_row.addStretch()
        self.calc_keys_widget = QWidget();
        calc_l = QVBoxLayout(self.calc_keys_widget);
        calc_l.addLayout(calc_row);
        key_layout.addWidget(self.calc_keys_widget)

        self.manual_keys_widget = QWidget();
        m_l = QVBoxLayout(self.manual_keys_widget)
        mr1 = QHBoxLayout();
        mr1.addWidget(QLabel("N:"));
        self.N_edit = QLineEdit();
        mr1.addWidget(self.N_edit)
        mr1.addWidget(QLabel("e:"));
        self.e_manual_edit = QLineEdit("65537");
        mr1.addWidget(self.e_manual_edit);
        m_l.addLayout(mr1)
        mr2 = QHBoxLayout();
        mr2.addWidget(QLabel("d:"));
        self.d_edit = QLineEdit();
        mr2.addWidget(self.d_edit)
        self.btn_set_manual_keys = QPushButton("✅ Установить ключи");
        self.btn_set_manual_keys.clicked.connect(self.set_manual_keys)
        mr2.addWidget(self.btn_set_manual_keys);
        mr2.addStretch();
        m_l.addLayout(mr2)
        self.manual_keys_widget.setVisible(False);
        key_layout.addWidget(self.manual_keys_widget)

        disp_row = QHBoxLayout()
        self.N_label = QLabel("N = ?");
        self.phi_label = QLabel("φ(N) = ?");
        self.d_label = QLabel("d = ?")
        disp_row.addWidget(self.N_label);
        disp_row.addWidget(self.phi_label);
        disp_row.addWidget(self.d_label);
        disp_row.addStretch()
        key_layout.addLayout(disp_row)

        key_file_row = QHBoxLayout()
        self.btn_load_keys = QPushButton("📥 Загрузить ключи");
        self.btn_load_keys.clicked.connect(self.load_keys_from_file)
        self.btn_save_keys = QPushButton("💾 Сохранить ключи");
        self.btn_save_keys.clicked.connect(self.save_keys_to_file)
        key_file_row.addWidget(self.btn_load_keys);
        key_file_row.addWidget(self.btn_save_keys);
        key_file_row.addStretch()
        key_layout.addLayout(key_file_row)
        key_group.setLayout(key_layout);
        outer.addWidget(key_group)

        data_group = QGroupBox("3. Данные и операции");
        data_layout = QVBoxLayout()
        splitter = QSplitter(Qt.Horizontal)
        left_group = QGroupBox("Входные данные (текст / числа / компактный HEX)")
        left_layout = QVBoxLayout(left_group)
        self.input_text_edit = QTextEdit();
        self.input_text_edit.setPlaceholderText("Введите текст, список чисел или компактный HEX шифр");
        self.input_text_edit.setFixedHeight(220)
        left_layout.addWidget(self.input_text_edit)
        left_btns = QHBoxLayout()
        self.btn_load_input = QPushButton("📥 Загрузить из файла");
        self.btn_load_input.clicked.connect(self.load_input_data)
        self.btn_clear_input = QPushButton("🗑 Очистить");
        self.btn_clear_input.clicked.connect(self.input_text_edit.clear)
        left_btns.addWidget(self.btn_load_input);
        left_btns.addWidget(self.btn_clear_input);
        left_btns.addStretch()
        left_layout.addLayout(left_btns)
        splitter.addWidget(left_group)

        right_group = QGroupBox("Выходные данные (компактный HEX или текст)")
        right_layout = QVBoxLayout(right_group)
        self.output_text_edit = QTextEdit();
        self.output_text_edit.setPlaceholderText("Результат...");
        self.output_text_edit.setFixedHeight(220)
        right_layout.addWidget(self.output_text_edit)
        right_btns = QHBoxLayout()
        self.btn_save_output = QPushButton("💾 Сохранить в файл");
        self.btn_save_output.clicked.connect(self.save_output_data)
        self.btn_clear_output = QPushButton("🗑 Очистить");
        self.btn_clear_output.clicked.connect(self.output_text_edit.clear)
        self.btn_copy_output = QPushButton("📋 Копировать");
        self.btn_copy_output.clicked.connect(self.copy_output)
        right_btns.addWidget(self.btn_save_output);
        right_btns.addWidget(self.btn_clear_output);
        right_btns.addWidget(self.btn_copy_output);
        right_btns.addStretch()
        right_layout.addLayout(right_btns)
        splitter.addWidget(right_group);
        splitter.setSizes([450, 450])
        data_layout.addWidget(splitter)

        log_group = QGroupBox("Лог операций / анимации");
        log_layout = QVBoxLayout(log_group)
        self.log_text_edit = QTextEdit();
        self.log_text_edit.setReadOnly(True);
        self.log_text_edit.setPlaceholderText("Логи...")
        self.log_text_edit.setMinimumHeight(350)  # Увеличена высота лога
        log_layout.addWidget(self.log_text_edit)
        log_btns = QHBoxLayout()
        self.btn_save_rsa_log = QPushButton("💾 Сохранить лог");
        self.btn_save_rsa_log.clicked.connect(self.save_rsa_log)
        self.btn_clear_rsa_log = QPushButton("🗑 Очистить лог");
        self.btn_clear_rsa_log.clicked.connect(self.log_text_edit.clear)
        self.btn_copy_rsa_log = QPushButton("📋 Копировать лог");
        self.btn_copy_rsa_log.clicked.connect(
            lambda: QApplication.clipboard().setText(self.log_text_edit.toPlainText()))
        log_btns.addWidget(self.btn_save_rsa_log);
        log_btns.addWidget(self.btn_copy_rsa_log);
        log_btns.addWidget(self.btn_clear_rsa_log);
        log_btns.addStretch()
        log_layout.addLayout(log_btns)
        data_layout.addWidget(log_group)

        ops_row = QHBoxLayout()
        self.btn_encrypt = QPushButton("🔒 Зашифровать (мгновенно)");
        self.btn_encrypt.clicked.connect(self.encrypt_rsa)
        self.btn_decrypt = QPushButton("🔓 Расшифровать (мгновенно)");
        self.btn_decrypt.clicked.connect(self.decrypt_rsa)
        ops_row.addWidget(self.btn_encrypt);
        ops_row.addWidget(self.btn_decrypt);
        ops_row.addStretch()
        data_layout.addLayout(ops_row)

        anim_group = QGroupBox("Анимация RSA (поблочно)");
        anim_layout = QVBoxLayout(anim_group)
        anim_btn_row = QHBoxLayout()
        self.btn_anim_enc = QPushButton("▶ Анимация шифрования");
        self.btn_anim_dec = QPushButton("▶ Анимация дешифрования")
        self.btn_anim_pause = QPushButton("⏸ Пауза");
        self.btn_anim_step = QPushButton("⏭ Шаг");
        self.btn_anim_stop = QPushButton("⏹ Стоп")
        for b in (self.btn_anim_pause, self.btn_anim_step, self.btn_anim_stop): b.setEnabled(False)
        anim_btn_row.addWidget(self.btn_anim_enc);
        anim_btn_row.addWidget(self.btn_anim_dec)
        anim_btn_row.addWidget(self.btn_anim_pause);
        anim_btn_row.addWidget(self.btn_anim_step);
        anim_btn_row.addWidget(self.btn_anim_stop);
        anim_btn_row.addStretch()
        anim_layout.addLayout(anim_btn_row)
        speed_row = QHBoxLayout();
        speed_row.addWidget(QLabel("Скорость:"))
        self.rsa_speed_slider = QSlider(Qt.Horizontal);
        self.rsa_speed_slider.setRange(1, 10);
        self.rsa_speed_slider.setValue(5);
        self.rsa_speed_slider.valueChanged.connect(self.update_rsa_timer_interval)
        speed_row.addWidget(self.rsa_speed_slider)
        self.rsa_progress = QProgressBar();
        self.rsa_progress.setMinimum(0);
        self.rsa_progress.setValue(0);
        speed_row.addWidget(self.rsa_progress)
        self.rsa_current_block_label = QLabel("Блок: -");
        speed_row.addWidget(self.rsa_current_block_label);
        speed_row.addStretch()
        anim_layout.addLayout(speed_row)
        data_layout.addWidget(anim_group)

        data_group.setLayout(data_layout);
        outer.addWidget(data_group)
        self.scroll_area.setWidget(container);
        main_layout.addWidget(self.scroll_area)

        self.N = None;
        self.phi = None;
        self.d = None;
        self.e_val = 65537
        self.blocks = [];
        self.block_bytes = None
        self.plain_lengths = [];
        self.total_plain_bytes = None
        self.cipher_blocks = []
        self.last_cipher_payload = None;
        self.last_output_kind = None

        self.rsa_anim_timer = QTimer(self);
        self.rsa_anim_timer.timeout.connect(self.rsa_animation_step)
        self.rsa_anim_running = False;
        self.rsa_anim_paused = False
        self.rsa_anim_mode = None
        self.rsa_anim_plain_blocks = [];
        self.rsa_anim_plain_lengths = []
        self.rsa_anim_cipher_blocks = []
        self.rsa_anim_index = 0;
        self.rsa_cipher_block_bytes = None

        self.btn_anim_enc.clicked.connect(lambda: self.start_rsa_animation('encrypt'))
        self.btn_anim_dec.clicked.connect(lambda: self.start_rsa_animation('decrypt'))
        self.btn_anim_pause.clicked.connect(self.toggle_rsa_pause)
        self.btn_anim_step.clicked.connect(self.rsa_animation_step_manual)
        self.btn_anim_stop.clicked.connect(self.stop_rsa_animation)

        self.bits_p_spin.valueChanged.connect(self.update_auto_method_label)
        self.bits_q_spin.valueChanged.connect(self.update_auto_method_label)
        self.method_p_combo.currentIndexChanged.connect(self.update_p_method_ui)
        self.method_q_combo.currentIndexChanged.connect(self.update_q_method_ui)

        self.on_key_mode_changed(0);
        self.on_generation_method_changed(0)
        self.update_auto_method_label()

    def update_p_method_ui(self):
        is_genpr = (self.method_p_combo.currentText() == "GENPR")
        self.bits_p_label.setVisible(not is_genpr)
        self.bits_p_spin.setVisible(not is_genpr)
        self.genpr_m_p_label.setVisible(is_genpr)
        self.genpr_m_p_spin.setVisible(is_genpr)
        self.genpr_k_p_label.setVisible(is_genpr)
        self.genpr_k_p_spin.setVisible(is_genpr)
        if self.gen_method_combo.currentIndex() == 0:
            self.method_q_combo.setCurrentIndex(self.method_p_combo.currentIndex())

    def update_q_method_ui(self):
        is_genpr = (self.method_q_combo.currentText() == "GENPR")
        self.bits_q_label.setVisible(not is_genpr)
        self.bits_q_spin.setVisible(not is_genpr)
        self.genpr_m_q_label.setVisible(is_genpr)
        self.genpr_m_q_spin.setVisible(is_genpr)
        self.genpr_k_q_label.setVisible(is_genpr)
        self.genpr_k_q_spin.setVisible(is_genpr)

    def detect_input_type(self, content):
        if not content or not content.strip(): return 'empty'
        s = content.strip()
        if self.N and re.fullmatch(r'[0-9a-fA-F]+', s):
            try:
                compact_hex_to_blocks(s, self.N);
                return 'compact_hex'
            except:
                pass
        allowed = set("[]{}(),; \t\r\n0123456789+")
        if all(ch in allowed for ch in s):
            try:
                blocks = parse_numbers(s)
                if blocks: return 'blocks'
            except:
                pass
        return 'text'

    def auto_select_method(self, bits: int, combo):
        t = combo.currentText()
        if t == "Миллер–Рабин": return "miller-rabin"
        if t == "Перебор": return "trial"
        if t == "Решето": return "sieve"
        if t == "GENPR": return "genpr"
        if t == "Авто":
            if bits <= METHOD_MAX_BITS.get("sieve", 0): return "sieve"
            if bits <= METHOD_MAX_BITS.get("trial", 0): return "trial"
            return "miller-rabin"
        return "miller-rabin"

    def update_auto_method_label(self):
        pass

    def on_generation_method_changed(self, index):
        if index == 2:
            self.btn_gen_pq.setEnabled(False)
            for w in [self.bits_p_label, self.bits_p_spin, self.method_p_label, self.method_p_combo,
                      self.bits_q_label, self.bits_q_spin, self.method_q_label, self.method_q_combo,
                      self.genpr_m_p_label, self.genpr_m_p_spin, self.genpr_k_p_label, self.genpr_k_p_spin,
                      self.genpr_m_q_label, self.genpr_m_q_spin, self.genpr_k_q_label, self.genpr_k_q_spin]:
                w.setVisible(False)
            return

        self.btn_gen_pq.setEnabled(True)
        self.method_p_label.setVisible(True);
        self.method_p_combo.setVisible(True)
        self.update_p_method_ui()

        if index == 0:
            self.bits_q_label.setVisible(False);
            self.bits_q_spin.setVisible(False)
            self.method_q_label.setVisible(False);
            self.method_q_combo.setVisible(False)
            self.genpr_m_q_label.setVisible(False);
            self.genpr_m_q_spin.setVisible(False)
            self.genpr_k_q_label.setVisible(False);
            self.genpr_k_q_spin.setVisible(False)
        else:
            self.method_q_label.setVisible(True);
            self.method_q_combo.setVisible(True)
            self.update_q_method_ui()

    def generate_pq(self):
        try:
            gm = self.gen_method_combo.currentIndex()
            if gm == 2:
                self.log_text_edit.append("[Генерация] Ручной режим: вводите p,q вручную.")
                return
            bits_p = self.bits_p_spin.value()
            method_p_str = self.auto_select_method(bits_p, self.method_p_combo)
            genpr_p = None
            if method_p_str == 'genpr':
                genpr_p = (self.genpr_m_p_spin.value(), self.genpr_k_p_spin.value())

            if gm == 0:
                bits_q = bits_p
                method_q_str = method_p_str
                genpr_q = genpr_p
            else:
                bits_q = self.bits_q_spin.value()
                method_q_str = self.auto_select_method(bits_q, self.method_q_combo)
                genpr_q = None
                if method_q_str == 'genpr':
                    genpr_q = (self.genpr_m_q_spin.value(), self.genpr_k_q_spin.value())

            p = generate_large_prime(bits_p, method_p_str, genpr_p)
            q = generate_large_prime(bits_q, method_q_str, genpr_q)

            attempts = 0
            while p == q and attempts < 10:
                q = generate_large_prime(bits_q, method_q_str, genpr_q)
                attempts += 1

            if p == q: raise ValueError("Не удалось получить разные p и q (попробуйте изменить параметры)")
            self.p_edit.setText(str(p));
            self.q_edit.setText(str(q))
            self.log_text_edit.append(f"[Генерация] Метод P: {method_p_str}, Метод Q: {method_q_str}\np={p}\nq={q}")
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def calculate_keys(self):
        try:
            p_txt = self.p_edit.text().strip();
            q_txt = self.q_edit.text().strip()
            if not p_txt or not q_txt: raise ValueError("Введите p и q")
            p = int(p_txt);
            q = int(q_txt);
            if p < 2 or q < 2 or p == q: raise ValueError("p,q ≥2 и различны")
            self.N = p * q;
            self.phi = (p - 1) * (q - 1)

            if self.auto_e_cb.isChecked():
                e_candidate = 65537
                if e_candidate >= self.phi:
                    e_candidate = 3

                while math.gcd(e_candidate, self.phi) != 1:
                    e_candidate += 2
                    if e_candidate >= self.phi:
                        raise ValueError("Не удалось автоматически подобрать e")

                e_val = e_candidate
                self.e_edit.setText(str(e_val))
            else:
                e_val = int(self.e_edit.text())
                if e_val <= 1 or e_val >= self.phi: raise ValueError("e вне диапазона")
                if math.gcd(e_val, self.phi) != 1: raise ValueError("e не взаимно просто с φ(N)")

            self.d = mod_inverse(e_val, self.phi);
            self.e_val = e_val
            self.N_label.setText(f"N={self.N}");
            self.phi_label.setText(f"φ(N)={self.phi}");
            self.d_label.setText(f"d={self.d}")
            self.blocks = [];
            self.block_bytes = None;
            self.plain_lengths = [];
            self.total_plain_bytes = None
            self.cipher_blocks = [];
            self.last_cipher_payload = None;
            self.last_output_kind = None

            self.log_text_edit.append("--- Генерация ключей ---")
            self.log_text_edit.append(f"1. Выбраны простые числа: p={p}, q={q}")
            self.log_text_edit.append(f"2. Модуль N = p * q = {p} * {q} = {self.N}")
            self.log_text_edit.append(f"3. Функция Эйлера phi(N) = (p-1)(q-1) = {self.phi}")
            self.log_text_edit.append(f"4. Экспонента e = {self.e_val} (взаимно проста с {self.phi})")
            self.log_text_edit.append(f"5. Секретная экспонента d = e^(-1) mod phi(N)")
            self.log_text_edit.append(f"   d = {self.d}")
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def on_key_mode_changed(self, index):
        self.calc_keys_widget.setVisible(index == 0)
        self.manual_keys_widget.setVisible(index == 1)

    def set_manual_keys(self):
        try:
            N = int(self.N_edit.text());
            e_val = int(self.e_manual_edit.text());
            d_val = int(self.d_edit.text())
            if N < 2 or e_val <= 1 or d_val <= 1: raise ValueError("Некорректные значения")
            self.N = N;
            self.e_val = e_val;
            self.d = d_val
            self.N_label.setText(f"N={self.N}");
            self.phi_label.setText("φ(N)=?");
            self.d_label.setText(f"d={self.d}")
            self.blocks = [];
            self.block_bytes = None;
            self.plain_lengths = [];
            self.total_plain_bytes = None
            self.cipher_blocks = [];
            self.last_cipher_payload = None;
            self.last_output_kind = None
            self.log_text_edit.append(f"[Ручные ключи] N={N} e={e_val} d={d_val}")
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def load_keys_from_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Загрузить ключи", "", "Text Files (*.txt);;All Files (*)")
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read().strip()
            if not content:
                QMessageBox.warning(self, "", "Файл пуст.");
                return
            N = e = d = None
            try:
                obj = json.loads(content)
                if isinstance(obj, dict):
                    N = obj.get("N");
                    e = obj.get("e");
                    d = obj.get("d")
            except json.JSONDecodeError:
                for line in content.splitlines():
                    line = line.strip()
                    if '=' in line:
                        k, v = line.split('=', 1)
                        k = k.lower().strip();
                        v = v.strip()
                        try:
                            if k == 'n':
                                N = int(v)
                            elif k == 'e':
                                e = int(v)
                            elif k == 'd':
                                d = int(v)
                        except:
                            pass
            if None in (N, e, d):
                QMessageBox.warning(self, "", "Не найдены N,e,d");
                return
            self.N_edit.setText(str(N));
            self.e_manual_edit.setText(str(e));
            self.d_edit.setText(str(d))
            self.set_manual_keys()
            self.log_text_edit.append(f"[Загрузка ключей] {path}")
        except Exception as ex:
            QMessageBox.critical(self, "Ошибка", f"Не удалось загрузить ключи:\n{ex}")

    def save_keys_to_file(self):
        if self.N is None or self.e_val is None or self.d is None:
            QMessageBox.warning(self, "", "Нет ключей");
            return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить ключи", "", "Text Files (*.txt)")
        if not path: return
        try:
            if self.plain_lengths and self.total_plain_bytes is not None:
                payload = {
                    "N": self.N,
                    "e": self.e_val,
                    "d": self.d,
                    "block_bytes": self.block_bytes,
                    "plain_lengths": self.plain_lengths,
                    "total_plain_bytes": self.total_plain_bytes
                }
                with open(path, 'w', encoding='utf-8') as f:
                    json.dump(payload, f, ensure_ascii=False, indent=2)
                self.log_text_edit.append(f"[Сохранено ключи+мета JSON] {path}")
            else:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(f"N={self.N}\ne={self.e_val}\nd={self.d}\n")
                self.log_text_edit.append(f"[Сохранено ключи TXT] {path}")
        except Exception as ex:
            QMessageBox.critical(self, "Ошибка", f"Не удалось сохранить:\n{ex}")

    def verify_cipher_metadata(self, payload):
        warnings = []
        if self.N is not None and payload.get("N") != self.N:
            warnings.append("N отличается от сохранённого.")
        if payload.get("e") is not None and self.e_val is not None and payload.get("e") != self.e_val:
            warnings.append("e отличается от сохранённого.")
        if payload.get("d") and self.d and payload.get("d") != self.d:
            warnings.append("d отличается от сохранённого.")
        if warnings:
            self.log_text_edit.append("[Предупреждение ключей] " + "; ".join(warnings))

    def encrypt_rsa(self):
        try:
            if self.N is None: raise ValueError("Нет N")
            content = self.input_text_edit.toPlainText().strip()
            if not content: raise ValueError("Нет данных")
            if self.detect_input_type(content) != 'text':
                raise ValueError("Для шифрования требуется текст.")
            self.blocks, self.block_bytes, self.plain_lengths, self.total_plain_bytes = encode_text_to_blocks(content,
                                                                                                              self.N)
            e = int(self.e_edit.text())
            if self.phi and (e <= 1 or e >= self.phi): raise ValueError("e вне диапазона")
            self.cipher_blocks = [mod_exp(m, e, self.N) for m in self.blocks]
            compact_hex = blocks_to_compact_hex(self.cipher_blocks, self.N)
            cbb = (self.N.bit_length() + 7) // 8
            log = []
            for i, m in enumerate(self.blocks):
                # Для отображения в логе:
                try:
                    m_bytes = m.to_bytes(self.plain_lengths[i], 'big')
                except OverflowError:
                    actual_len = (m.bit_length() + 7) // 8
                    m_bytes = m.to_bytes(actual_len, 'big')
                m_text = bytes_to_printable_utf8(m_bytes)

                c = self.cipher_blocks[i];
                log.append(f"--- Блок {i} ---")
                log.append(f"Сообщение (M): {m} (Hex: {m_bytes.hex().upper()}) -> '{m_text}'")
                log.append(f"Вычисление: {m}^{e} mod {self.N} = {c}")
                log.append(f"Шифртекст (C): {c}")

            self.log_text_edit.append('\n'.join(log))
            self.output_text_edit.setPlainText(compact_hex)
            self.last_output_kind = "cipher"
            self.last_cipher_payload = {
                "type": "rsa_cipher",
                "cipher": self.cipher_blocks,
                "block_bytes": self.block_bytes,
                "plain_lengths": self.plain_lengths,
                "total_plain_bytes": self.total_plain_bytes,
                "N": self.N,
                "e": e,
                "d": self.d if self.d is not None else None,
                "compact_hex": compact_hex
            }
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def decrypt_rsa(self):
        try:
            if self.N is None or self.d is None: raise ValueError("Нет ключей")
            content = self.input_text_edit.toPlainText().strip()
            if not content and self.cipher_blocks:
                cblocks = self.cipher_blocks
                plain_lengths = self.plain_lengths
                total_plain_bytes = self.total_plain_bytes
            else:
                t = self.detect_input_type(content)
                if t == 'compact_hex':
                    cblocks = compact_hex_to_blocks(content, self.N)
                    plain_lengths = self.plain_lengths
                    total_plain_bytes = self.total_plain_bytes
                elif t == 'blocks':
                    cblocks = parse_numbers(content);
                    plain_lengths = None;
                    total_plain_bytes = None
                else:
                    raise ValueError("Нужен компактный HEX или список чисел.")
            if any(c >= self.N for c in cblocks):
                QMessageBox.warning(self, "", "Есть блок >= N")
            plain = [mod_exp(c, self.d, self.N) for c in cblocks]
            bb = self.block_bytes or max(1, (self.N.bit_length() - 1) // 8)
            text = decode_blocks_to_text_precise(plain, bb, plain_lengths, total_plain_bytes)

            log = []
            for i, c in enumerate(cblocks):
                m = plain[i]
                plen = plain_lengths[i] if plain_lengths and i < len(plain_lengths) else bb

                # Для лога
                try:
                    m_bytes = m.to_bytes(plen, 'big')
                except OverflowError:
                    actual_len = (m.bit_length() + 7) // 8
                    m_bytes = m.to_bytes(actual_len, 'big')
                m_text = bytes_to_printable_utf8(m_bytes)

                log.append(f"--- Блок {i} ---")
                log.append(f"Шифртекст (C): {c}")
                log.append(f"Вычисление: {c}^{self.d} mod {self.N} = {m}")
                log.append(f"Расшифровано (M): {m} (Hex: {m_bytes.hex().upper()}) -> '{m_text}'")

            self.log_text_edit.append('\n'.join(log))
            self.output_text_edit.setPlainText(text)
            self.last_output_kind = "plain"
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def start_rsa_animation(self, mode):
        if self.rsa_anim_running:
            QMessageBox.warning(self, "", "Анимация уже идёт");
            return
        if self.N is None:
            QMessageBox.warning(self, "", "Нет ключей");
            return
        content = self.input_text_edit.toPlainText().strip()
        if not content and mode == 'encrypt':
            QMessageBox.warning(self, "", "Нет данных");
            return
        try:
            self.rsa_anim_mode = mode;
            self.log_text_edit.append(f"[Анимация RSA] {mode}")
            if mode == 'encrypt':
                if self.detect_input_type(content) != 'text':
                    raise ValueError("Для анимации нужен текст.")
                self.rsa_anim_plain_blocks, self.block_bytes, self.rsa_anim_plain_lengths, _ = encode_text_to_blocks(
                    content, self.N)
                self.e_val = int(self.e_edit.text())
                self.rsa_anim_cipher_blocks = []
                self.rsa_cipher_block_bytes = (self.N.bit_length() + 7) // 8
                total = len(self.rsa_anim_plain_blocks)
                self.log_text_edit.append(f"Блоков: {total}")
            else:
                dtype = self.detect_input_type(content)
                if dtype == 'compact_hex':
                    self.rsa_anim_cipher_blocks = compact_hex_to_blocks(content, self.N)
                elif dtype == 'blocks':
                    self.rsa_anim_cipher_blocks = parse_numbers(content)
                else:
                    raise ValueError("Для дешифрования анимации нужен компактный HEX или числа.")
                self.rsa_cipher_block_bytes = (self.N.bit_length() + 7) // 8
                self.rsa_anim_plain_blocks = []
                self.rsa_anim_plain_lengths = []
                total = len(self.rsa_anim_cipher_blocks)
                self.log_text_edit.append(f"Шифр-блоков: {total}")
            self.rsa_anim_index = 0
            self.rsa_progress.setMaximum(total);
            self.rsa_progress.setValue(0)
            self.rsa_current_block_label.setText("Блок: 0")
            self.output_text_edit.clear()
            self.rsa_anim_running = True;
            self.rsa_anim_paused = False
            for b in (self.btn_anim_pause, self.btn_anim_step, self.btn_anim_stop): b.setEnabled(True)
            self.btn_anim_enc.setEnabled(False);
            self.btn_anim_dec.setEnabled(False)
            self.update_rsa_timer_interval();
            self.rsa_anim_timer.start()
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def update_rsa_timer_interval(self):
        val = self.rsa_speed_slider.value();
        interval = 1100 - val * 100
        if interval < 50: interval = 50
        self.rsa_anim_timer.setInterval(interval)

    def rsa_animation_step(self):
        if not self.rsa_anim_running or self.rsa_anim_paused: return
        self._rsa_do_step()

    def rsa_animation_step_manual(self):
        if not self.rsa_anim_running: return
        if not self.rsa_anim_paused:
            self.rsa_anim_timer.stop();
            self.rsa_anim_paused = True;
            self.btn_anim_pause.setText("▶ Продолжить")
        self._rsa_do_step()

    def _rsa_do_step(self):
        if self.rsa_anim_mode == 'encrypt':
            total = len(self.rsa_anim_plain_blocks)
            if self.rsa_anim_index >= total: self.finish_rsa_animation(); return
            m = self.rsa_anim_plain_blocks[self.rsa_anim_index]

            # Лог с буквами
            m_len = self.rsa_anim_plain_lengths[self.rsa_anim_index]
            try:
                m_bytes = m.to_bytes(m_len, 'big')
            except OverflowError:
                actual_len = (m.bit_length() + 7) // 8
                m_bytes = m.to_bytes(actual_len, 'big')
            m_text = bytes_to_printable_utf8(m_bytes)

            c = mod_exp(m, self.e_val, self.N)
            self.rsa_anim_cipher_blocks.append(c)
            current_hex = blocks_to_compact_hex(self.rsa_anim_cipher_blocks, self.N)
            self.output_text_edit.setPlainText(current_hex)

            self.log_text_edit.append(f"--- Блок {self.rsa_anim_index} ---")
            self.log_text_edit.append(f"M = {m} (Hex: {m_bytes.hex().upper()}) -> '{m_text}'")
            self.log_text_edit.append(f"{m}^{self.e_val} mod {self.N} = {c}")
            self.log_text_edit.append(f"C = {c}")

            self.rsa_anim_index += 1
        else:
            total = len(self.rsa_anim_cipher_blocks)
            if self.rsa_anim_index >= total: self.finish_rsa_animation(); return
            c = self.rsa_anim_cipher_blocks[self.rsa_anim_index]
            m = mod_exp(c, self.d, self.N)
            self.rsa_anim_plain_blocks.append(m)
            pb_len = self.block_bytes or max(1, (self.N.bit_length() - 1) // 8)

            # Лог с буквами
            try:
                m_bytes = m.to_bytes(pb_len, 'big')
            except OverflowError:
                actual_len = (m.bit_length() + 7) // 8
                m_bytes = m.to_bytes(actual_len, 'big')
            m_text = bytes_to_printable_utf8(m_bytes)

            text_so_far = decode_blocks_to_text(self.rsa_anim_plain_blocks, pb_len)
            self.output_text_edit.setPlainText(text_so_far)

            self.log_text_edit.append(f"--- Блок {self.rsa_anim_index} ---")
            self.log_text_edit.append(f"C = {c}")
            self.log_text_edit.append(f"{c}^{self.d} mod {self.N} = {m}")
            self.log_text_edit.append(f"M = {m} (Hex: {m_bytes.hex().upper()}) -> '{m_text}'")

            self.rsa_anim_index += 1

        self.rsa_progress.setValue(self.rsa_anim_index);
        self.rsa_current_block_label.setText(f"Блок: {self.rsa_anim_index}")
        if self.rsa_anim_mode == 'encrypt' and self.rsa_anim_index >= len(self.rsa_anim_plain_blocks):
            self.finish_rsa_animation()
        if self.rsa_anim_mode == 'decrypt' and self.rsa_anim_index >= len(self.rsa_anim_cipher_blocks):
            self.finish_rsa_animation()

    def toggle_rsa_pause(self):
        if not self.rsa_anim_running: return
        if self.rsa_anim_paused:
            self.rsa_anim_paused = False;
            self.btn_anim_pause.setText("⏸ Пауза");
            self.rsa_anim_timer.start()
        else:
            self.rsa_anim_paused = True;
            self.btn_anim_pause.setText("▶ Продолжить");
            self.rsa_anim_timer.stop()

    def finish_rsa_animation(self):
        self.rsa_anim_timer.stop()
        tail = "Готово: компактный HEX." if self.rsa_anim_mode == 'encrypt' else "Готово: расшифрованный текст."
        self.log_text_edit.append(f"[Завершено RSA] {tail}")
        self.rsa_anim_running = False;
        self.rsa_anim_paused = False
        for b in (self.btn_anim_pause, self.btn_anim_step, self.btn_anim_stop): b.setEnabled(False)
        self.btn_anim_enc.setEnabled(True);
        self.btn_anim_dec.setEnabled(True);
        self.btn_anim_pause.setText("⏸ Пауза")

    def stop_rsa_animation(self):
        if not self.rsa_anim_running: return
        self.rsa_anim_timer.stop();
        self.log_text.append("[Остановлено RSA]")
        self.rsa_anim_running = False;
        self.rsa_anim_paused = False
        for b in (self.btn_anim_pause, self.btn_anim_step, self.btn_anim_stop): b.setEnabled(False)
        self.btn_anim_enc.setEnabled(True);
        self.btn_anim_dec.setEnabled(True);
        self.btn_anim_pause.setText("⏸ Пауза")

    def load_input_data(self):
        path, _ = QFileDialog.getOpenFileName(self, "Загрузить вход", "", "Text Files (*.txt);;All Files (*)")
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read().strip()
            if not content:
                QMessageBox.warning(self, "", "Файл пуст.");
                return
            payload = None
            try:
                payload = json.loads(content)
            except json.JSONDecodeError:
                pass
            if isinstance(payload, dict) and payload.get("type") == "rsa_cipher":
                self.cipher_blocks = payload.get("cipher", [])
                self.block_bytes = payload.get("block_bytes")
                self.plain_lengths = payload.get("plain_lengths") or []
                self.total_plain_bytes = payload.get("total_plain_bytes")
                self.verify_cipher_metadata(payload)
                compact = payload.get("compact_hex")
                self.input_text_edit.setPlainText(compact if compact else ', '.join(map(str, self.cipher_blocks)))
                self.last_cipher_payload = payload;
                self.last_output_kind = "cipher"
                self.log_text_edit.append(f"[Загрузка шифра] {path}")
                return
            self.input_text_edit.setPlainText(content);
            self.log_text_edit.append(f"[Загрузка входа] {path}")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Загрузка:\n{e}")

    def save_output_data(self):
        content = self.output_text_edit.toPlainText().strip()
        if not content:
            QMessageBox.warning(self, "", "Нет данных.");
            return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить выход", "", "Text Files (*.txt)")
        if not path: return
        try:
            if self.last_output_kind == "cipher" and self.last_cipher_payload:
                payload = dict(self.last_cipher_payload);
                payload["compact_hex"] = content
                with open(path, 'w', encoding='utf-8') as f:
                    json.dump(payload, f, ensure_ascii=False, indent=2)
            else:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(content)
            self.log_text_edit.append(f"[Сохранение] {path}")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Сохранение:\n{e}")

    def copy_output(self):
        txt = self.output_text.toPlainText()
        if not txt: QMessageBox.warning(self, "", "Пусто"); return
        QApplication.clipboard().setText(txt)

    def save_rsa_log(self):
        log = self.log_text_edit.toPlainText().strip()
        if not log:
            QMessageBox.warning(self, "", "Лог пуст.");
            return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить лог RSA", "", "Text Files (*.txt)")
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(log)
                self.log_text_edit.append(f"[Лог сохранён] {path}")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Сохранение:\n{e}")


# -------------------- RSALibraryTab (OAEP) --------------------
class RSALibraryTab(QWidget):
    def __init__(self):
        super().__init__()
        self.private_key = None;
        self.public_key = None
        outer = QVBoxLayout(self)

        key_group = QGroupBox("1. Ключи RSA (библиотека)");
        key_layout = QVBoxLayout()
        row = QHBoxLayout();
        row.addWidget(QLabel("Битность:"))
        self.lib_bits_spin = QSpinBox();
        self.lib_bits_spin.setRange(512, 4096);
        self.lib_bits_spin.setValue(2048);
        row.addWidget(self.lib_bits_spin)
        self.btn_lib_generate = QPushButton("🎲 Сгенерировать пару ключей");
        self.btn_lib_generate.clicked.connect(self.lib_generate_keys);
        row.addWidget(self.btn_lib_generate);
        row.addStretch();
        key_layout.addLayout(row)
        keys_row = QHBoxLayout()
        self.pub_key_edit = QTextEdit();
        self.pub_key_edit.setPlaceholderText("Публичный ключ (PEM)")
        self.priv_key_edit = QTextEdit();
        self.priv_key_edit.setPlaceholderText("Приватный ключ (PEM)")
        keys_row.addWidget(self.pub_key_edit);
        keys_row.addWidget(self.priv_key_edit);
        key_layout.addLayout(keys_row)
        key_btns = QHBoxLayout()
        btn_load_pub = QPushButton("📥 Загрузить публичный");
        btn_load_pub.clicked.connect(self.lib_load_public_key)
        btn_save_pub = QPushButton("💾 Сохранить публичный");
        btn_save_pub.clicked.connect(self.lib_save_public_key)
        btn_load_priv = QPushButton("📥 Загрузить приватный");
        btn_load_priv.clicked.connect(self.lib_load_private_key)
        btn_save_priv = QPushButton("💾 Сохранить приватный");
        btn_save_priv.clicked.connect(self.lib_save_private_key)
        key_btns.addWidget(btn_load_pub);
        key_btns.addWidget(btn_save_pub);
        key_btns.addWidget(btn_load_priv);
        key_btns.addWidget(btn_save_priv);
        key_btns.addStretch()
        key_layout.addLayout(key_btns);
        key_group.setLayout(key_layout);
        outer.addWidget(key_group)

        data_group = QGroupBox("2. Данные");
        data_layout = QVBoxLayout()
        splitter = QSplitter(Qt.Horizontal)
        left_box = QGroupBox("Вход (текст / Base64 блоки)");
        left_layout = QVBoxLayout(left_box)
        self.input_edit = QTextEdit();
        self.input_edit.setPlaceholderText("Текст или Base64 блоки");
        left_layout.addWidget(self.input_edit)
        left_btns = QHBoxLayout()
        self.btn_load_input_lib = QPushButton("📥 Загрузить вход");
        self.btn_load_input_lib.clicked.connect(self.load_library_input_file)
        self.btn_clear_input_lib = QPushButton("🗑 Очистить вход");
        self.btn_clear_input_lib.clicked.connect(self.input_edit.clear)
        left_btns.addWidget(self.btn_load_input_lib);
        left_btns.addWidget(self.btn_clear_input_lib);
        left_btns.addStretch();
        left_layout.addLayout(left_btns)
        splitter.addWidget(left_box)

        right_box = QGroupBox("Выход");
        right_layout = QVBoxLayout(right_box)
        self.output_edit = QTextEdit();
        self.output_edit.setPlaceholderText("Результат");
        right_layout.addWidget(self.output_edit)
        right_btns = QHBoxLayout()
        self.btn_save_output_lib = QPushButton("💾 Сохранить выход");
        self.btn_save_output_lib.clicked.connect(self.save_library_output_file)
        self.btn_copy_output_lib = QPushButton("📋 Копировать выход");
        self.btn_copy_output_lib.clicked.connect(
            lambda: QApplication.clipboard().setText(self.output_edit.toPlainText()))
        self.btn_clear_output_lib = QPushButton("🗑 Очистить выход");
        self.btn_clear_output_lib.clicked.connect(self.output_edit.clear)
        right_btns.addWidget(self.btn_save_output_lib);
        right_btns.addWidget(self.btn_copy_output_lib);
        right_btns.addWidget(self.btn_clear_output_lib);
        right_btns.addStretch()
        right_layout.addLayout(right_btns);
        splitter.addWidget(right_box)
        splitter.setSizes([500, 500]);
        data_layout.addWidget(splitter)

        act_row = QHBoxLayout()
        self.btn_lib_encrypt = QPushButton("🔒 Зашифровать (OAEP)");
        self.btn_lib_encrypt.clicked.connect(self.lib_encrypt)
        self.btn_lib_decrypt = QPushButton("🔓 Расшифровать (OAEP)");
        self.btn_lib_decrypt.clicked.connect(self.lib_decrypt)
        act_row.addWidget(self.btn_lib_encrypt);
        act_row.addWidget(self.btn_lib_decrypt);
        act_row.addStretch();
        data_layout.addLayout(act_row)
        self.lib_status_label = QLabel("Готово.");
        data_layout.addWidget(self.lib_status_label)
        data_group.setLayout(data_layout);
        outer.addWidget(data_group)

    def set_status(self, text):
        self.lib_status_label.setText(text)

    def ensure_public_key(self):
        if self.public_key: return self.public_key
        pem = self.pub_key_edit.toPlainText().strip()
        if not pem: raise ValueError("Публичный ключ не задан.")
        self.public_key = serialization.load_pem_public_key(pem.encode('utf-8'));
        return self.public_key

    def ensure_private_key(self):
        if self.private_key: return self.private_key
        pem = self.priv_key_edit.toPlainText().strip()
        if not pem: raise ValueError("Приватный ключ не задан.")
        self.private_key = serialization.load_pem_private_key(pem.encode('utf-8'), password=None);
        return self.private_key

    def lib_generate_keys(self):
        try:
            bits = self.lib_bits_spin.value()
            priv = crypto_rsa.generate_private_key(public_exponent=65537, key_size=bits)
            pub = priv.public_key()
            priv_pem = priv.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.TraditionalOpenSSL,
                                          serialization.NoEncryption()).decode('utf-8')
            pub_pem = pub.public_bytes(serialization.Encoding.PEM,
                                       serialization.PublicFormat.SubjectPublicKeyInfo).decode('utf-8')
            self.private_key = priv;
            self.public_key = pub
            self.priv_key_edit.setPlainText(priv_pem);
            self.pub_key_edit.setPlainText(pub_pem)
            self.set_status(f"Новая пара ключей {bits} бит.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", str(e))

    def lib_load_public_key(self):
        path, _ = QFileDialog.getOpenFileName(self, "Загрузить публичный ключ", "", "PEM Files (*.pem);;All Files (*)")
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                pem = f.read()
            self.pub_key_edit.setPlainText(pem);
            self.public_key = serialization.load_pem_public_key(pem.encode('utf-8'))
            self.set_status("Публичный ключ загружен.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Загрузка:\n{e}")

    def lib_save_public_key(self):
        pem = self.pub_key_edit.toPlainText().strip()
        if not pem: QMessageBox.warning(self, "⚠️", "Нет публичного ключа."); return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить публичный ключ", "", "PEM Files (*.pem);;All Files (*)")
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(pem)
                self.set_status("Публичный ключ сохранён.")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Сохранение:\n{e}")

    def lib_load_private_key(self):
        path, _ = QFileDialog.getOpenFileName(self, "Загрузить приватный ключ", "", "PEM Files (*.pem);;All Files (*)")
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                pem = f.read()
            self.priv_key_edit.setPlainText(pem);
            self.private_key = serialization.load_pem_private_key(pem.encode('utf-8'), password=None)
            self.set_status("Приватный ключ загружен.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Загрузка:\n{e}")

    def lib_save_private_key(self):
        pem = self.priv_key_edit.toPlainText().strip()
        if not pem: QMessageBox.warning(self, "⚠️", "Нет приватного ключа."); return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить приватный ключ", "", "PEM Files (*.pem);;All Files (*)")
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(pem)
                self.set_status("Приватный ключ сохранён.")
            except Exception as e:
                QMessageBox.critical(self, "❌ Ошибка", f"Сохранение:\n{e}")

    def _chunk_encrypt(self, public_key, data_bytes, hash_alg=hashes.SHA256()):
        key_bytes = public_key.key_size // 8;
        h_len = hash_alg.digest_size
        max_chunk = key_bytes - 2 * h_len - 2
        if max_chunk <= 0: raise ValueError("Ключ слишком мал для OAEP.")
        chunks = [data_bytes[i:i + max_chunk] for i in range(0, len(data_bytes), max_chunk)]
        out = []
        for ch in chunks:
            enc = public_key.encrypt(ch, crypto_padding.OAEP(mgf=crypto_padding.MGF1(hash_alg), algorithm=hash_alg,
                                                             label=None))
            out.append(base64.b64encode(enc).decode('utf-8'))
        return out

    def _chunk_decrypt(self, private_key, cipher_text, hash_alg=hashes.SHA256()):
        lines = [l.strip() for l in cipher_text.replace('\r', '').split('\n') if l.strip()]
        if not lines: raise ValueError("Нет данных.")
        buf = bytearray()
        for line in lines:
            enc = base64.b64decode(line)
            dec = private_key.decrypt(enc, crypto_padding.OAEP(mgf=crypto_padding.MGF1(hash_alg), algorithm=hash_alg,
                                                               label=None))
            buf.extend(dec)
        return bytes(buf)

    def lib_encrypt(self):
        try:
            pub = self.ensure_public_key()
            txt = self.input_edit.toPlainText()
            if not txt: raise ValueError("Введите текст.")
            chunks = self._chunk_encrypt(pub, txt.encode('utf-8'))
            self.output_edit.setPlainText('\n'.join(chunks))
            self.set_status(f"Зашифровано {len(chunks)} блок(ов).")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", str(e))

    def lib_decrypt(self):
        try:
            priv = self.ensure_private_key()
            cipher = self.input_edit.toPlainText().strip()
            if not cipher: raise ValueError("Введите Base64 блоки.")
            for ln in [l for l in cipher.splitlines() if l.strip()]:
                try:
                    base64.b64decode(ln)
                except:
                    raise ValueError("Некорректный Base64.")
            data = self._chunk_decrypt(priv, cipher)
            self.output_edit.setPlainText(data.decode('utf-8', 'replace'))
            self.set_status("Расшифровано.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", str(e))

    def load_library_input_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Загрузить вход", "", "Text Files (*.txt);;All Files (*)")
        if not path: return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
            if not content.strip():
                QMessageBox.warning(self, "⚠️", "Файл пуст.");
                return
            self.input_edit.setPlainText(content);
            self.set_status("Вход загружен.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Загрузка:\n{e}")

    def save_library_output_file(self):
        content = self.output_edit.toPlainText().strip()
        if not content:
            QMessageBox.warning(self, "⚠️", "Нет данных.");
            return
        path, _ = QFileDialog.getSaveFileName(self, "Сохранить выход", "", "Text Files (*.txt)")
        if not path: return
        try:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(content)
            self.set_status("Выход сохранён.")
        except Exception as e:
            QMessageBox.critical(self, "❌ Ошибка", f"Сохранение:\n{e}")


# -------------------- Главное окно --------------------
class CryptoSuite(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Криптографический практикум (ПЗ-9..12)")
        self.resize(1280, 880)
        central = QWidget();
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        tabs = QTabWidget()
        tabs.addTab(GammaTab(), "🔒 ПЗ-9: Гаммирование")
        tabs.addTab(ModArithmeticTab(), "🧮 ПЗ-10: Модулярная арифметика")
        tabs.addTab(RSATab(), "🔐 ПЗ-11: RSA (полная)")
        tabs.addTab(RSALibraryTab(), "🔐 ПЗ-12: RSA (библиотека)")
        layout.addWidget(tabs)
        self.apply_style_light()
        self.create_menu()

    def create_menu(self):
        menubar = QMenuBar(self)
        view = menubar.addMenu("Вид")
        act_light = QAction("Светлая тема", self)
        act_dark = QAction("Тёмная тема", self)
        act_light.triggered.connect(self.apply_style_light)
        act_dark.triggered.connect(self.apply_style_dark)
        view.addAction(act_light);
        view.addAction(act_dark)
        self.setMenuBar(menubar)

    def apply_common_styles(self):
        font = QFont("Segoe UI", 10);
        self.setFont(font)
        self.setStyleSheet(self.styleSheet() + """
        QGroupBox {border:1px solid #b0b0b0;border-radius:8px;margin-top:12px;padding:8px;font-weight:bold;}
        QGroupBox::title {subcontrol-origin: margin;subcontrol-position: top left;padding:0 6px;}
        QPushButton {padding:6px 12px;border-radius:6px;font-weight:500;}
        QLineEdit, QTextEdit, QSpinBox, QComboBox {border:1px solid #b8b8b8;border-radius:6px;padding:4px;}
        QTabBar::tab {padding:6px 14px;margin:4px;border-radius:6px;font-weight:500;}
        QSplitter::handle {background:#d2d2d2;}
        """)

    def apply_style_light(self):
        palette = QPalette()
        palette.setColor(QPalette.Window, QColor("#F7F9FA"))
        palette.setColor(QPalette.WindowText, QColor("#202124"))
        palette.setColor(QPalette.Base, QColor("#FFFFFF"))
        palette.setColor(QPalette.AlternateBase, QColor("#EFF2F5"))
        palette.setColor(QPalette.Text, QColor("#202124"))
        palette.setColor(QPalette.Button, QColor("#4A73F3"))
        palette.setColor(QPalette.ButtonText, QColor("#FFFFFF"))
        palette.setColor(QPalette.Highlight, QColor("#4A73F3"))
        palette.setColor(QPalette.HighlightedText, QColor("#FFFFFF"))
        self.setPalette(palette)
        self.setStyleSheet("""
        QPushButton {background-color:#4A73F3;color:#ffffff;}
        QPushButton:hover {background-color:#335ee0;}
        QPushButton:pressed {background-color:#284bb9;}
        QTabBar::tab {background:#E1E5EC;color:#1F2225;}
        QTabBar::tab:selected {background:#4A73F3;color:#fff;}
        QLineEdit, QTextEdit, QSpinBox, QComboBox {background:#FFFFFF;color:#202124;}
        """)
        self.apply_common_styles()

    def apply_style_dark(self):
        palette = QPalette()
        palette.setColor(QPalette.Window, QColor("#1E2127"))
        palette.setColor(QPalette.WindowText, QColor("#E6E6E6"))
        palette.setColor(QPalette.Base, QColor("#2B2F36"))
        palette.setColor(QPalette.AlternateBase, QColor("#323841"))
        palette.setColor(QPalette.Text, QColor("#E0E0E0"))
        palette.setColor(QPalette.Button, QColor("#5865F2"))
        palette.setColor(QPalette.ButtonText, QColor("#FFFFFF"))
        palette.setColor(QPalette.Highlight, QColor("#5865F2"))
        palette.setColor(QPalette.HighlightedText, QColor("#000000"))
        self.setPalette(palette)
        self.setStyleSheet("""
        QPushButton {background-color:#5865F2;color:#ffffff;}
        QPushButton:hover {background-color:#4752c4;}
        QPushButton:pressed {background-color:#3942a1;}
        QTabBar::tab {background:#3b3f46;color:#ddd;}
        QTabBar::tab:selected {background:#5865F2;color:#fff;}
        QLineEdit, QTextEdit, QSpinBox, QComboBox {background:#2e3138;color:#ddd;border:1px solid #555;}
        """)
        self.apply_common_styles()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = CryptoSuite()
    window.show()
    sys.exit(app.exec())
