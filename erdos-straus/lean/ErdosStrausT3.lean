import Mathlib

/-!
# Эрдёш–Штраус: критерий для t = 3

Пусть p — простое, p > 3, p ≡ 1 (mod 4), q = (p+3)/4 и N = p·q. Тогда

  ∃ y z > 0, 4/p = 1/q + 1/y + 1/z   ⟺   у N есть простой делитель r ≡ 2 (mod 3).

Следствие для p ≡ 1 (mod 3), куда попадают все «трудные» классы по модулю 840:
условие эквивалентно тому, что такой делитель есть у q = (p+3)/4.
-/

namespace ErdosStrausT3

lemma prime_mod_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : p % 3 = 1 ∨ p % 3 = 2 := by
  have : p % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  omega

lemma N_mod_three {p q : ℕ} (hp : p.Prime) (h3 : 3 < p) (h4q : 4 * q = p + 3) :
    (p * q) % 3 = 1 := by
  have hq : q % 3 = p % 3 := by omega
  rw [Nat.mul_mod, hq]
  rcases prime_mod_three hp h3 with h | h <;> simp [h]

/-- Если все простые делители `d` сравнимы с 1 по модулю 3, то и `d ≡ 1 (mod 3)`. -/
lemma mod3_eq_one_of_primes :
    ∀ d : ℕ, d ≠ 0 → (∀ r, r.Prime → r ∣ d → r % 3 = 1) → d % 3 = 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd h
    by_cases h1 : d = 1
    · subst h1; rfl
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
      have ihk := ih k hklt hk0 (fun r hr hrk => h r hr (hrk.trans (Dvd.intro_left d.minFac hk.symm)))
      rw [show d % 3 = (d.minFac * k) % 3 from congrArg (· % 3) hk, Nat.mul_mod,
        h _ hmp (Nat.minFac_dvd d), ihk]

/-- Рациональное тождество: 1/q + 3/(p q) = 4/p при 4q = p + 3. -/
lemma key_rat {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (h4q : 4 * q = p + 3) :
    (1 : ℚ) / q + 3 / (p * q) = 4 / p := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h4q' : (4 : ℚ) * q = p + 3 := by exact_mod_cast h4q
  rw [div_add_div _ _ hq' (mul_ne_zero hp' hq'), div_eq_div_iff (mul_ne_zero hq' (mul_ne_zero hp' hq')) hp']
  linear_combination (-(q * p : ℚ)) * h4q'

/-- Достаточность: по простому `r ∣ p q`, `r ≡ 2 (mod 3)`, явно строим `y` и `z`. -/
theorem sufficiency (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (hp4 : p % 4 = 1)
    (hd : ∃ r : ℕ, r.Prime ∧ r ∣ p * ((p + 3) / 4) ∧ r % 3 = 2) :
    ∃ y z : ℕ, 0 < y ∧ 0 < z ∧
      (4 : ℚ) / p = 1 / (((p + 3) / 4 : ℕ) : ℚ) + 1 / y + 1 / z := by
  obtain ⟨r, hr, hrN, hr3⟩ := hd
  set q : ℕ := (p + 3) / 4 with hq_def
  have h4q : 4 * q = p + 3 := Nat.mul_div_cancel' (by omega)
  set N : ℕ := p * q with hN_def
  have hpp : 0 < p := hp.pos
  have hqp : 0 < q := by omega
  have hNp : 0 < N := Nat.mul_pos hpp hqp
  have hN3 : N % 3 = 1 := N_mod_three hp h3 h4q
  have hrN2 : r ∣ N ^ 2 := dvd_pow hrN two_ne_zero
  set M : ℕ := N ^ 2 / r with hM_def
  have hrM : r * M = N ^ 2 := Nat.mul_div_cancel' hrN2
  have hM3 : M % 3 = 2 := by
    have h : (r * M) % 3 = 1 := by rw [hrM, pow_two, Nat.mul_mod, hN3]
    rw [Nat.mul_mod, hr3] at h
    omega
  obtain ⟨y, hy⟩ : 3 ∣ N + r := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z, hz⟩ : 3 ∣ N + M := Nat.dvd_of_mod_eq_zero (by omega)
  have hyp : 0 < y := by omega
  have hzp : 0 < z := by nlinarith [hz, hNp, Nat.zero_le M]
  refine ⟨y, z, hyp, hzp, ?_⟩
  have hy' : (y : ℚ) = (N + r) / 3 := by
    have : ((N + r : ℕ) : ℚ) = 3 * y := by exact_mod_cast hy
    push_cast at this; linarith
  have hz' : (z : ℚ) = (N + M) / 3 := by
    have : ((N + M : ℕ) : ℚ) = 3 * z := by exact_mod_cast hz
    push_cast at this; linarith
  have hrM' : (r : ℚ) * M = (N : ℚ) ^ 2 := by exact_mod_cast hrM
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hyp.ne'
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hzp.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hNp.ne'
  have hyz : (1 : ℚ) / y + 1 / z = 3 / N := by
    rw [div_add_div _ _ hyq hzq, div_eq_div_iff (mul_ne_zero hyq hzq) hNq, hy', hz']
    linear_combination (-1 / 3 : ℚ) * hrM'
  have hfin := key_rat hpp hqp h4q
  have hNcast : (N : ℚ) = (p : ℚ) * q := by rw [hN_def]; push_cast; ring
  rw [add_assoc, hyz, hNcast, hfin]

/-- Необходимость: если решение с x = q есть, то у N есть простой делитель ≡ 2 (mod 3). -/
theorem necessity (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (hp4 : p % 4 = 1)
    (hsol : ∃ y z : ℕ, 0 < y ∧ 0 < z ∧
      (4 : ℚ) / p = 1 / (((p + 3) / 4 : ℕ) : ℚ) + 1 / y + 1 / z) :
    ∃ r : ℕ, r.Prime ∧ r ∣ p * ((p + 3) / 4) ∧ r % 3 = 2 := by
  obtain ⟨y, z, hyp, hzp, heq⟩ := hsol
  set q : ℕ := (p + 3) / 4 with hq_def
  have h4q : 4 * q = p + 3 := Nat.mul_div_cancel' (by omega)
  set N : ℕ := p * q with hN_def
  have hpp : 0 < p := hp.pos
  have hqp : 0 < q := by omega
  have hNp : 0 < N := Nat.mul_pos hpp hqp
  have hN3 : N % 3 = 1 := N_mod_three hp h3 h4q
  -- 1/y + 1/z = 3/N
  have hNcast : (N : ℚ) = (p : ℚ) * q := by rw [hN_def]; push_cast; ring
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hyp.ne'
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hzp.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hNp.ne'
  have hyz : (1 : ℚ) / y + 1 / z = 3 / N := by
    have hfin := key_rat hpp hqp h4q
    rw [hNcast]; linarith
  rw [div_add_div _ _ hyq hzq, div_eq_div_iff (mul_ne_zero hyq hzq) hNq] at hyz
  have hnat : (z + y) * N = 3 * (y * z) := by
    have : ((1 : ℚ) * z + y * 1) * N = 3 * (y * z) := hyz
    simp only [one_mul, mul_one] at this
    exact_mod_cast this
  -- 3y > N и 3z > N
  have hy3 : N < 3 * y := by
    by_contra hc; push Not at hc
    nlinarith [Nat.mul_le_mul_right z hc, Nat.mul_pos hyp hNp]
  have hz3 : N < 3 * z := by
    by_contra hc; push Not at hc
    nlinarith [Nat.mul_le_mul_right y hc, Nat.mul_pos hzp hNp]
  obtain ⟨d, hd⟩ : ∃ d, 3 * y = N + d := ⟨3 * y - N, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, 3 * z = N + e := ⟨3 * z - N, by omega⟩
  -- d * e = N^2
  have hde : d * e = N ^ 2 := by
    have hd' : (3 : ℤ) * y = N + d := by exact_mod_cast hd
    have he' : (3 : ℤ) * z = N + e := by exact_mod_cast he
    have hn' : ((z : ℤ) + y) * N = 3 * (y * z) := by exact_mod_cast hnat
    have : (d : ℤ) * e = (N : ℤ) ^ 2 := by
      linear_combination (-(e : ℤ)) * hd' + (-(3 * (y : ℤ) - N)) * he' + (-3 : ℤ) * hn'
    exact_mod_cast this
  have hd3 : d % 3 = 2 := by omega
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : N ^ 2 = 0 := by rw [← hde, zero_mul]
    have := pow_pos hNp 2
    omega
  -- если бы все простые делители d были ≡ 1 (mod 3), то d ≡ 1 — противоречие
  by_contra hno
  push Not at hno
  have hall : ∀ r, r.Prime → r ∣ d → r % 3 = 1 := by
    intro r hr hrd
    have hrN : r ∣ N := hr.dvd_of_dvd_pow (hde ▸ dvd_mul_of_dvd_left hrd e)
    have h2 := hno r hr hrN
    have h0 : r % 3 ≠ 0 := by
      intro h0
      have : r = 3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
        (Nat.dvd_of_mod_eq_zero h0) |>.symm
      subst this
      omega
    omega
  have := mod3_eq_one_of_primes d hd0 hall
  omega

/-- Главная теорема: критерий для t = 3. -/
theorem criterion (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (hp4 : p % 4 = 1) :
    (∃ y z : ℕ, 0 < y ∧ 0 < z ∧
      (4 : ℚ) / p = 1 / (((p + 3) / 4 : ℕ) : ℚ) + 1 / y + 1 / z) ↔
    (∃ r : ℕ, r.Prime ∧ r ∣ p * ((p + 3) / 4) ∧ r % 3 = 2) :=
  ⟨necessity p hp h3 hp4, sufficiency p hp h3 hp4⟩

/-- Следствие для p ≡ 1 (mod 3) (все «трудные» классы): делитель должен быть у (p+3)/4. -/
theorem criterion_hard (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (hp4 : p % 4 = 1)
    (hp3 : p % 3 = 1) :
    (∃ y z : ℕ, 0 < y ∧ 0 < z ∧
      (4 : ℚ) / p = 1 / (((p + 3) / 4 : ℕ) : ℚ) + 1 / y + 1 / z) ↔
    (∃ r : ℕ, r.Prime ∧ r ∣ (p + 3) / 4 ∧ r % 3 = 2) := by
  rw [criterion p hp h3 hp4]
  constructor
  · rintro ⟨r, hr, hrN, hr3⟩
    refine ⟨r, hr, ?_, hr3⟩
    rcases (Nat.Prime.dvd_mul hr).mp hrN with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      subst this; omega
    · exact h
  · rintro ⟨r, hr, hrq, hr3⟩
    exact ⟨r, hr, dvd_mul_of_dvd_right hrq p, hr3⟩

end ErdosStrausT3

#print axioms ErdosStrausT3.criterion
#print axioms ErdosStrausT3.criterion_hard
