# Независимая проверка двух доказательств в Lean 4

Проверка выполнена 26 ноября 2026 года на облачном Linux-сервере (15 ГБ RAM).
Оба доказательства собраны с нуля из исходников. Готовые результаты авторов
не использовались, кроме стандартного кэша библиотеки Mathlib.

## 1. Гипотеза Римана (и GRH для L-функций Дирихле)

| | |
|---|---|
| Репозиторий | `lsernau/grh-lean`, папка `grh-compact/` (короткая версия) |
| Коммит | `72fead102f663d5c7a407964a13dc0cf9d977207` |
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Объём | 796 файлов `.lean`, около 113 тыс. строк |
| Сборка | `lake build`: 9843 задачи, **0 ошибок**, 5347 с, пик памяти около 5,9 ГБ |
| `sorry` | **0** в собранном коде |
| Поиск подозрительного кода | нет `axiom`, `unsafe`, `opaque`, `native_decide`, `#eval` |

Проверка аксиом (`lake env lean scripts/PrintAxioms.lean`):

```
'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'riemannZeta_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_ne_zero_of_half_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re_of_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Формулировка `RiemannHypothesis` взята из самой Mathlib
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, строка 185). Авторы её не определяли:

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## 2. Опровержение ETH (Exponential Time Hypothesis)

| | |
|---|---|
| Репозиторий | `anthropics/formal-math`, папка `eth/` |
| Коммит | `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` |
| Lean | `leanprover/lean4:v4.33.1` |
| Сборка | `lake build`: 9768 задач, **0 ошибок**, 934 с, пик памяти около 2,8 ГБ |
| `sorry` | только два, в файле `Challenge.lean`. Это шаблон задачи, так и задумано |

```
'MainResults.ethIsFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainResults.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Определение: `def ETH : Prop := 0 < s 3`, `def ETHIsFalse : Prop := ¬ ETH`.
Здесь `s k` — точная нижняя грань показателей δ, при которых k-SAT решается
за время O(2^(δn)) на машинах Тьюринга TM2 из Mathlib.

## Что эта проверка доказывает и чего не доказывает

- ✅ Ядро Lean приняло оба доказательства. Логических дыр, пропусков и
  нестандартных аксиом нет.
- ✅ Доказаны именно стандартные формулировки, подмены условий нет.
- ⚠️ Lean проверяет логику, а не смысл определений в Mathlib. Ошибка в самой
  Mathlib теоретически возможна, хотя очень маловероятна.
- ⚠️ Мы проверяли только стандартным ядром Lean. Независимые проверщики
  (nanoda, lean4lean и др.) здесь не запускались. По данным MIT, они тоже
  приняли доказательство.
- ⚠️ Человеческое понимание доказательства и рецензирование ещё идут.
- ⚠️ Проверку проводила модель Anthropic (Claude). Для ETH это конфликт
  интересов, поэтому решающий аргумент — вывод программы Lean, приведённый
  выше, а не мнение модели.

## Как повторить

```bash
git clone https://github.com/lsernau/grh-lean && cd grh-lean/grh-compact
git checkout 72fead102f663d5c7a407964a13dc0cf9d977207
lake exe cache get        # кэш Mathlib (нужен доступ к cache.mathlib.org)
ulimit -s unlimited
lake build
lake env lean scripts/PrintAxioms.lean
```

Полные журналы сборки лежат в папке [`logs/`](logs/).
