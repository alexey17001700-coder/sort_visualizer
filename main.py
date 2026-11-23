# -*- coding: utf-8 -*-
"""
ВИЗУАЛИЗАТОР АЛГОРИТМОВ СОРТИРОВКИ
Автор: Штаб (Цифровой Архитектор)
Запуск:  python main.py

Что умеет:
  • 6 алгоритмов: пузырёк, выбор, вставки, быстрая, слияние, куча
  • настройка размера массива и скорости анимации
  • подсветка сравниваемых элементов и уже отсортированной части
  • счётчик шагов, сравнений и времени работы
  • клавиши: Space — старт/пауза, R — новый массив
"""

import colorsys
import random
import time
import tkinter as tk
from tkinter import ttk

# ─────────────────────────── АЛГОРИТМЫ ───────────────────────────
# Каждый алгоритм — генератор. Он отдаёт кадры: (массив, активные, откуда отсортировано)
# sorted_from = индекс, с которого массив уже отсортирован (None — ещё нет)


def bubble_sort(a):
    n = len(a)
    for i in range(n - 1):
        swapped = False
        for j in range(n - 1 - i):
            yield a, [j, j + 1], n - i
            if a[j] > a[j + 1]:
                a[j], a[j + 1] = a[j + 1], a[j]
                swapped = True
                yield a, [j, j + 1], n - i
        if not swapped:
            break
    yield a, [], 0


def selection_sort(a):
    n = len(a)
    for i in range(n):
        m = i
        for j in range(i + 1, n):
            yield a, [m, j], i
            if a[j] < a[m]:
                m = j
        if m != i:
            a[i], a[m] = a[m], a[i]
        yield a, [i], i + 1
    yield a, [], 0


def insertion_sort(a):
    n = len(a)
    for i in range(1, n):
        key = a[i]
        j = i - 1
        while j >= 0 and a[j] > key:
            a[j + 1] = a[j]
            j -= 1
            yield a, [j + 1, j + 2], None
        a[j + 1] = key
        yield a, [j + 1], None
    yield a, [], 0


def quick_sort(a):
    def partition(lo, hi):
        pivot = a[hi]
        i = lo - 1
        for j in range(lo, hi):
            yield a, [j, hi], None
            if a[j] <= pivot:
                i += 1
                a[i], a[j] = a[j], a[i]
                yield a, [i, j], None
        a[i + 1], a[hi] = a[hi], a[i + 1]
        yield a, [i + 1], None
        return i + 1

    def qs(lo, hi):
        if lo < hi:
            p = yield from partition(lo, hi)
            yield from qs(lo, p - 1)
            yield from qs(p + 1, hi)

    yield from qs(0, len(a) - 1)
    yield a, [], 0


def merge_sort(a):
    def ms(lo, hi):
        if hi - lo < 2:
            return
        mid = (lo + hi) // 2
        yield from ms(lo, mid)
        yield from ms(mid, hi)
        left = a[lo:mid]
        right = a[mid:hi]
        i = j = 0
        k = lo
        while i < len(left) and j < len(right):
            if left[i] <= right[j]:
                a[k] = left[i]
                i += 1
            else:
                a[k] = right[j]
                j += 1
            k += 1
            yield a, [k - 1], None
        while i < len(left):
            a[k] = left[i]
            i += 1
            k += 1
            yield a, [k - 1], None
        while j < len(right):
            a[k] = right[j]
            j += 1
            k += 1
            yield a, [k - 1], None

    yield from ms(0, len(a))
    yield a, [], 0


def heap_sort(a):
    n = len(a)

    def sift(i, size):
        while True:
            l, r = 2 * i + 1, 2 * i + 2
            m = i
            if l < size and a[l] > a[m]:
                m = l
            if r < size and a[r] > a[m]:
                m = r
            if m == i:
                break
            a[i], a[m] = a[m], a[i]
            yield a, [i, m], None
            i = m

    for i in range(n // 2 - 1, -1, -1):
        yield from sift(i, n)
    for end in range(n - 1, 0, -1):
        a[0], a[end] = a[end], a[0]
        yield a, [0, end], end
        yield from sift(0, end)
    yield a, [], 0


ALGOS = {
    "Пузырёк (Bubble)": bubble_sort,
    "Выбор (Selection)": selection_sort,
    "Вставки (Insertion)": insertion_sort,
    "Быстрая (Quick)": quick_sort,
    "Слияние (Merge)": merge_sort,
    "Куча (Heap)": heap_sort,
}

# ─────────────────────────── ЦВЕТА ───────────────────────────
BG = "#0e1116"
CANVAS_BG = "#12161d"
PANEL = "#171c25"
TEXT = "#e6edf3"
MUTED = "#8b98a9"
ACCENT = "#3b82f6"
ACTIVE = "#f87171"
SORTED = "#22c55e"


def bar_color(value, max_value):
    """Плавный градиент синий → голубой → фиолетовый по величине."""
    t = value / max_value
    hue = 0.58 - 0.28 * t          # 0.58 (синий) → 0.30 (бирюза)
    r, g, b = colorsys.hls_to_rgb(hue, 0.55, 0.75)
    return "#%02x%02x%02x" % (int(r * 255), int(g * 255), int(b * 255))


# ─────────────────────────── ПРИЛОЖЕНИЕ ───────────────────────────
class SortVisualizer:
    def __init__(self, root):
        self.root = root
        root.title("Визуализатор сортировок · Штаб")
        root.geometry("1000x660")
        root.minsize(680, 460)
        root.configure(bg=BG)

        self.n = 60
        self.values = []
        self.gen = None
        self.running = False
        self.active = set()
        self.sorted_from = None
        self.steps = 0
        self.started_at = 0.0
        self.elapsed = 0.0
        self.finished = False

        self._build_ui()
        self.new_array()

        root.bind("<space>", lambda e: self.toggle())
        root.bind("<r>", lambda e: self.new_array())
        root.bind("<R>", lambda e: self.new_array())

    # ── интерфейс ──
    def _build_ui(self):
        head = tk.Frame(self.root, bg=BG)
        head.pack(fill="x", padx=14, pady=(12, 6))

        tk.Label(head, text="ВИЗУАЛИЗАТОР АЛГОРИТМОВ СОРТИРОВКИ",
                 bg=BG, fg=TEXT, font=("Segoe UI", 15, "bold")).pack(side="left")
        self.stats = tk.Label(head, text="", bg=BG, fg=MUTED,
                              font=("Consolas", 10))
        self.stats.pack(side="right")

        self.canvas = tk.Canvas(self.root, bg=CANVAS_BG, highlightthickness=0)
        self.canvas.pack(fill="both", expand=True, padx=14, pady=6)
        self.canvas.bind("<Configure>", lambda e: self.draw())

        panel = tk.Frame(self.root, bg=PANEL)
        panel.pack(fill="x", padx=14, pady=(0, 12))
        inner = tk.Frame(panel, bg=PANEL)
        inner.pack(fill="x", padx=12, pady=10)

        # алгоритм
        tk.Label(inner, text="Алгоритм", bg=PANEL, fg=MUTED,
                 font=("Segoe UI", 9)).grid(row=0, column=0, sticky="w")
        self.algo = ttk.Combobox(inner, values=list(ALGOS.keys()),
                                 state="readonly", width=20)
        self.algo.current(0)
        self.algo.grid(row=1, column=0, padx=(0, 16), sticky="w")
        self.algo.bind("<<ComboboxSelected>>", lambda e: self.reset_run())

        # размер
        tk.Label(inner, text="Размер массива", bg=PANEL, fg=MUTED,
                 font=("Segoe UI", 9)).grid(row=0, column=1, sticky="w")
        self.size_var = tk.IntVar(value=self.n)
        tk.Scale(inner, from_=10, to=200, orient="horizontal", variable=self.size_var,
                 bg=PANEL, fg=TEXT, troughcolor=CANVAS_BG, highlightthickness=0,
                 length=170, showvalue=True, command=self._size_changed
                 ).grid(row=1, column=1, padx=(0, 16), sticky="w")

        # скорость
        tk.Label(inner, text="Скорость", bg=PANEL, fg=MUTED,
                 font=("Segoe UI", 9)).grid(row=0, column=2, sticky="w")
        self.speed_var = tk.IntVar(value=70)
        tk.Scale(inner, from_=1, to=100, orient="horizontal", variable=self.speed_var,
                 bg=PANEL, fg=TEXT, troughcolor=CANVAS_BG, highlightthickness=0,
                 length=170, showvalue=True).grid(row=1, column=2, padx=(0, 16), sticky="w")

        # кнопки
        btns = tk.Frame(inner, bg=PANEL)
        btns.grid(row=0, column=3, rowspan=2, padx=(8, 0))

        self.btn_run = tk.Button(btns, text="▶  Старт", command=self.toggle,
                                 bg=ACCENT, fg="white", relief="flat", width=11,
                                 font=("Segoe UI", 10, "bold"), cursor="hand2",
                                 activebackground="#2563eb", activeforeground="white")
        self.btn_run.pack(side="left", padx=4)

        tk.Button(btns, text="🔄  Новый массив", command=self.new_array,
                  bg="#2a3341", fg=TEXT, relief="flat", width=15,
                  font=("Segoe UI", 10), cursor="hand2",
                  activebackground="#38445a", activeforeground=TEXT
                  ).pack(side="left", padx=4)

        tk.Button(btns, text="⏹  Сброс", command=self.reset_run,
                  bg="#2a3341", fg=TEXT, relief="flat", width=9,
                  font=("Segoe UI", 10), cursor="hand2",
                  activebackground="#38445a", activeforeground=TEXT
                  ).pack(side="left", padx=4)

        tk.Label(self.root, text="Пробел — старт/пауза   ·   R — новый массив",
                 bg=BG, fg=MUTED, font=("Segoe UI", 9)
                 ).pack(anchor="w", padx=16, pady=(0, 8))

    # ── данные ──
    def new_array(self):
        self.reset_run(silent=True)
        n = self.size_var.get()
        self.values = [random.randint(5, 100) for _ in range(n)]
        self.finished = False
        self.draw()
        self.update_stats()

    def _size_changed(self, _=None):
        # защита от раннего вызова: слайдер дёргает команду ещё до сборки кнопок
        if not hasattr(self, "btn_run"):
            return
        if self.size_var.get() != len(self.values):
            self.new_array()

    def reset_run(self, silent=False):
        self.running = False
        self.gen = None
        self.active = set()
        self.sorted_from = None
        self.steps = 0
        self.elapsed = 0.0
        self.finished = False
        self.btn_run.config(text="▶  Старт")
        if not silent:
            self.draw()
            self.update_stats()

    def toggle(self):
        if self.finished:
            return
        if self.running:
            self.running = False
            self.btn_run.config(text="▶  Старт")
            self.update_stats()
        else:
            if self.gen is None:
                self.gen = ALGOS[self.algo.get()](self.values)
                self.started_at = time.time()
            self.running = True
            self.btn_run.config(text="⏸  Пауза")
            self.tick()

    def delay(self):
        """Скорость 1..100 → задержка 120..1 мс."""
        return max(1, int(120 * (1 - self.speed_var.get() / 100.0)) + 1)

    # ── цикл анимации ──
    def tick(self):
        if not self.running or self.gen is None:
            return
        try:
            arr, active, sorted_from = next(self.gen)
        except StopIteration:
            self.running = False
            self.finished = True
            self.active = set()
            self.sorted_from = 0
            self.elapsed = time.time() - self.started_at
            self.btn_run.config(text="✔  Готово")
            self.draw()
            self.update_stats()
            return

        self.active = set(active)
        self.sorted_from = sorted_from
        self.steps += 1
        self.elapsed = time.time() - self.started_at
        self.draw()
        self.update_stats()
        self.root.after(self.delay(), self.tick)

    # ── отрисовка ──
    def draw(self):
        c = self.canvas
        c.delete("all")
        w = c.winfo_width()
        h = c.winfo_height()
        if w < 10 or h < 10 or not self.values:
            return

        pad = 10
        n = len(self.values)
        maxv = max(self.values) or 1
        slot = (w - pad * 2) / n
        bw = max(1.0, slot * 0.82)
        gap = (slot - bw) / 2
        base = h - pad

        for i, v in enumerate(self.values):
            x0 = pad + i * slot + gap
            x1 = x0 + bw
            y0 = base - (h - pad * 2 - 24) * (v / maxv)
            if i in self.active:
                color = ACTIVE
            elif self.sorted_from is not None and i >= self.sorted_from:
                color = SORTED
            else:
                color = bar_color(v, maxv)
            c.create_rectangle(x0, y0, x1, base, fill=color, outline="")

        # подпись максимума
        c.create_text(pad, 12, anchor="w", text=f"макс {maxv}", fill=MUTED,
                      font=("Consolas", 9))

    def update_stats(self):
        txt = (f"шагов: {self.steps}   ·   элементов: {len(self.values)}"
               f"   ·   время: {self.elapsed:.2f} с")
        if self.finished:
            txt += "   ·   СОРТИРОВКА ЗАВЕРШЕНА"
        self.stats.config(text=txt)


def main():
    root = tk.Tk()
    try:
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TCombobox", fieldbackground="#222b36", background="#222b36",
                        foreground=TEXT, arrowcolor=TEXT, bordercolor="#2a3341")
        style.map("TCombobox", fieldbackground=[("readonly", "#222b36")],
                  foreground=[("readonly", TEXT)])
    except Exception:
        pass
    SortVisualizer(root)
    root.mainloop()


if __name__ == "__main__":
    main()
