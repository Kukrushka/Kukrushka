import Mathlib

/-!
# Эрдёш–Штраус: общая необходимость и критерий для t = 7

Пусть t — простое, 4q = p + t и N = p·q. Решение 4/p = 1/q + 1/y + 1/z равносильно
существованию делителя d ∣ N², для которого d ≡ −N (mod t).

* `necessity`: при t ≡ 3 (mod 4) и t ∤ N у N обязан быть простой делитель, который является
  невычетом по модулю t.
* `t7_criterion`: для «трудных» p (p ≡ 1 mod 8, p — вычет по модулю 7) решение с
  x = (p+7)/4 существует ⟺ у (p+7)/4 есть простой делитель ≡ 3, 5 или 6 (mod 7).
-/

namespace ErdosStrausGeneral

/-- Если все простые делители `d` — квадраты по модулю `t`, то и `d` — квадрат. -/
lemma isSquare_of_primes (t : ℕ) :
    ∀ d : ℕ, d ≠ 0 → (∀ r, r.Prime → r ∣ d → IsSquare (r : ZMod t)) →
      IsSquare (d : ZMod t) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd h
    by_cases h1 : d = 1
    · subst h1; exact ⟨1, by simp⟩
    · have hmp : d.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd d
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact hd hk
      have hklt : k < d := by
        have h2 := hmp.two_le
        have hkpos := Nat.pos_of_ne_zero hk0
        nlinarith [hk]
      have ihk := ih k hklt hk0
        (fun r hr hrk => h r hr (hrk.trans (Dvd.intro_left d.minFac hk.symm)))
      have hcast : (d : ZMod t) = (d.minFac : ZMod t) * (k : ZMod t) := by
        rw [← Nat.cast_mul, ← hk]
      rw [hcast]
      exact (h _ hmp (Nat.minFac_dvd d)).mul ihk

/-- 4/p − 1/q = t/(p q) при 4q = p + t. -/
lemma sub_eq {p q t : ℕ} (hp : 0 < p) (hq : 0 < q) (h4q : 4 * q = p + t) :
    (4 : ℚ) / p - 1 / q = t / (p * q) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h4q' : (4 : ℚ) * q = p + t := by exact_mod_cast h4q
  rw [div_sub_div _ _ hp' hq', div_eq_div_iff (mul_ne_zero hp' hq') (mul_ne_zero hp' hq')]
  linear_combination ((p : ℚ) * q) * h4q'

/-- Из решения получаем (z + y)·N = t·y·z. -/
lemma reduce {p q t y z : ℕ} (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) (hz : 0 < z)
    (h4q : 4 * q = p + t) (heq : (4 : ℚ) / p = 1 / q + 1 / y + 1 / z) :
    (z + y) * (p * q) = t * (y * z) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hz.ne'
  have key : (1 : ℚ) / y + 1 / z = t / (p * q) := by
    rw [← sub_eq hp hq h4q, heq]; ring
  rw [div_add_div _ _ hy' hz', div_eq_div_iff (mul_ne_zero hy' hz') (mul_ne_zero hp' hq')] at key
  have h2 : (((z + y) * (p * q) : ℕ) : ℚ) = ((t * (y * z) : ℕ) : ℚ) := by
    push_cast; linear_combination key
  exact_mod_cast h2

/-- **Общая необходимость** для простого t ≡ 3 (mod 4). -/
theorem necessity (t p q : ℕ) [Fact t.Prime] (ht4 : t % 4 = 3) (hp : 0 < p) (hq : 0 < q)
    (h4q : 4 * q = p + t) (htN : ¬ t ∣ p * q)
    (hsol : ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ (4 : ℚ) / p = 1 / q + 1 / y + 1 / z) :
    ∃ r : ℕ, r.Prime ∧ r ∣ p * q ∧ ¬ IsSquare (r : ZMod t) := by
  obtain ⟨y, z, hyp, hzp, heq⟩ := hsol
  set N := p * q with hN_def
  have hNp : 0 < N := Nat.mul_pos hp hq
  have hnat := reduce hp hq hyp hzp h4q heq
  have ht0 : 0 < t := (Fact.out : t.Prime).pos
  have hy3 : N < t * y := by
    by_contra hc; push Not at hc
    nlinarith [Nat.mul_le_mul_right z hc, Nat.mul_pos hyp hNp]
  have hz3 : N < t * z := by
    by_contra hc; push Not at hc
    nlinarith [Nat.mul_le_mul_right y hc, Nat.mul_pos hzp hNp]
  obtain ⟨d, hd⟩ : ∃ d, t * y = N + d := ⟨t * y - N, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, t * z = N + e := ⟨t * z - N, by omega⟩
  have hde : d * e = N ^ 2 := by
    have hd' : (t : ℤ) * y = N + d := by exact_mod_cast hd
    have he' : (t : ℤ) * z = N + e := by exact_mod_cast he
    have hn' : ((z : ℤ) + y) * N = t * (y * z) := by exact_mod_cast hnat
    have : (d : ℤ) * e = (N : ℤ) ^ 2 := by
      linear_combination (-(e : ℤ)) * hd' + (-((t : ℤ) * y - N)) * he' + (-(t : ℤ)) * hn'
    exact_mod_cast this
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : N ^ 2 = 0 := by rw [← hde, zero_mul]
    have := pow_pos hNp 2
    omega
  -- d ≡ −N (mod t)
  have hdmod : (d : ZMod t) = -(N : ZMod t) := by
    have h := congrArg (Nat.cast : ℕ → ZMod t) hd
    push_cast at h
    rw [ZMod.natCast_self, zero_mul] at h
    linear_combination -h
  have hN0 : (N : ZMod t) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact htN
  by_contra hno
  push Not at hno
  -- все простые делители N — квадраты
  have hNsq : IsSquare (N : ZMod t) := isSquare_of_primes t N hNp.ne' hno
  have hdsq : IsSquare (d : ZMod t) := isSquare_of_primes t d hd0 (fun r hr hrd =>
    hno r hr (hr.dvd_of_dvd_pow (hde ▸ dvd_mul_of_dvd_left hrd e)))
  rw [hdmod] at hdsq
  obtain ⟨a, ha⟩ := hdsq
  obtain ⟨b, hb⟩ := hNsq
  have hm1 : IsSquare (-1 : ZMod t) :=
    ⟨a * b⁻¹, by
      rw [show a * b⁻¹ * (a * b⁻¹) = (a * a) * (b * b)⁻¹ by ring, ← ha, ← hb, neg_mul,
        mul_inv_cancel₀ hN0]⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hm1) ht4

/-- **Общая достаточность**: по делителю d ∣ N² с d ≡ −N (mod t) строим решение. -/
theorem sufficiency_of_divisor (t p q d : ℕ) [Fact t.Prime] (hp : 0 < p) (hq : 0 < q)
    (h4q : 4 * q = p + t) (htN : ¬ t ∣ p * q) (hd0 : 0 < d) (hdN : d ∣ (p * q) ^ 2)
    (hdmod : (d : ZMod t) = -((p * q : ℕ) : ZMod t)) :
    ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ (4 : ℚ) / p = 1 / q + 1 / y + 1 / z := by
  set N := p * q with hN_def
  have hNp : 0 < N := Nat.mul_pos hp hq
  have ht0 : 0 < t := (Fact.out : t.Prime).pos
  obtain ⟨M, hM⟩ := hdN
  have hN0 : (N : ZMod t) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact htN
  have hMmod : (M : ZMod t) = -(N : ZMod t) := by
    have h := congrArg (Nat.cast : ℕ → ZMod t) hM
    push_cast at h
    rw [hdmod] at h
    apply mul_left_cancel₀ hN0
    linear_combination h
  obtain ⟨y, hy⟩ : t ∣ N + d := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hdmod]; ring
  obtain ⟨z, hz⟩ : t ∣ N + M := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hMmod]; ring
  have hyp : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h, mul_zero] at hy; omega
    · exact h
  have hzp : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h, mul_zero] at hz; omega
    · exact h
  refine ⟨y, z, hyp, hzp, ?_⟩
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hyp.ne'
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hzp.ne'
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hyq : (t : ℚ) * y = N + d := by exact_mod_cast hy.symm
  have hzq : (t : ℚ) * z = N + M := by exact_mod_cast hz.symm
  have hMq : (N : ℚ) ^ 2 = d * M := by exact_mod_cast hM
  have hNq : (N : ℚ) = p * q := by rw [hN_def]; push_cast; ring
  have hG : ((z : ℚ) + y) * N = t * (y * z) := by
    apply mul_left_cancel₀ ht'
    linear_combination hMq + (-((t : ℚ) * y - N)) * hzq + (-(M : ℚ)) * hyq
  have key : (1 : ℚ) / y + 1 / z = t / (p * q) := by
    rw [div_add_div _ _ hy' hz', div_eq_div_iff (mul_ne_zero hy' hz') (mul_ne_zero hp' hq'), ← hNq]
    linear_combination hG
  have hs := sub_eq hp hq h4q
  linarith

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma isSquare_mod7 (n : ℕ) (h : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4) :
    IsSquare (n : ZMod 7) := by
  rw [← ZMod.natCast_mod]
  rcases h with h | h | h | h <;> rw [h] <;> decide

lemma t7_table : ∀ a b : ZMod 7, (a = 3 ∨ a = 5 ∨ a = 6) → (b = 1 ∨ b = 2 ∨ b = 4) →
    ∃ k : Fin 3, a * 2 ^ (k : ℕ) = -(b * (2 * b)) := by decide

/-- **Критерий для t = 7** на «трудных» простых. -/
theorem t7_criterion (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 1)
    (hp7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) :
    (∃ y z : ℕ, 0 < y ∧ 0 < z ∧
      (4 : ℚ) / p = 1 / (((p + 7) / 4 : ℕ) : ℚ) + 1 / y + 1 / z) ↔
    (∃ r : ℕ, r.Prime ∧ r ∣ (p + 7) / 4 ∧ (r % 7 = 3 ∨ r % 7 = 5 ∨ r % 7 = 6)) := by
  set q := (p + 7) / 4 with hq_def
  have h4q : 4 * q = p + 7 := Nat.mul_div_cancel' (by omega)
  have hpp : 0 < p := hp.pos
  have hqp : 0 < q := by omega
  have h7N : ¬ 7 ∣ p * q := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h <;> omega
  constructor
  · intro hsol
    obtain ⟨r, hr, hrN, hrsq⟩ := necessity 7 p q (by norm_num) hpp hqp h4q h7N hsol
    have hr7 : r % 7 = 3 ∨ r % 7 = 5 ∨ r % 7 = 6 := by
      by_contra hc
      exact hrsq (isSquare_mod7 r (by omega))
    refine ⟨r, hr, ?_, hr7⟩
    rcases (Nat.Prime.dvd_mul hr).mp hrN with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      subst this; omega
    · exact h
  · rintro ⟨r, hr, hrq, hr7⟩
    have h2q : 2 ∣ q := by omega
    have hr2 : r ≠ 2 := by rintro rfl; omega
    have h2r : 2 * r ∣ q :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd
        ((Nat.coprime_primes (by norm_num) hr).mpr (Ne.symm hr2)) h2q hrq
    -- остатки в ZMod 7
    have hq7 : (q : ZMod 7) = 2 * p := by
      have h := congrArg (Nat.cast : ℕ → ZMod 7) h4q
      push_cast at h
      have h7 : (7 : ZMod 7) = 0 := rfl
      linear_combination 2 * h + (2 - (q : ZMod 7)) * h7
    have ha : (r : ZMod 7) = 3 ∨ (r : ZMod 7) = 5 ∨ (r : ZMod 7) = 6 := by
      rw [← ZMod.natCast_mod]
      rcases hr7 with h | h | h <;> rw [h] <;> simp
    have hb : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 2 ∨ (p : ZMod 7) = 4 := by
      rw [← ZMod.natCast_mod]
      rcases hp7 with h | h | h <;> rw [h] <;> simp
    obtain ⟨k, hk⟩ := t7_table _ _ ha hb
    refine sufficiency_of_divisor 7 p q (r * 2 ^ (k : ℕ)) hpp hqp h4q h7N
      (Nat.mul_pos hr.pos (by positivity)) ?_ ?_
    · have hk2 : 2 ^ (k : ℕ) ∣ 4 := by
        have : (k : ℕ) ≤ 2 := by omega
        exact (Nat.pow_dvd_pow 2 this)
      calc r * 2 ^ (k : ℕ) ∣ r * 4 := mul_dvd_mul_left r hk2
        _ ∣ (2 * r) ^ 2 := ⟨r, by ring⟩
        _ ∣ q ^ 2 := pow_dvd_pow_of_dvd h2r 2
        _ ∣ (p * q) ^ 2 := pow_dvd_pow_of_dvd (dvd_mul_left q p) 2
    · push_cast
      rw [hk, hq7]

end ErdosStrausGeneral

#print axioms ErdosStrausGeneral.necessity
#print axioms ErdosStrausGeneral.sufficiency_of_divisor
#print axioms ErdosStrausGeneral.t7_criterion
