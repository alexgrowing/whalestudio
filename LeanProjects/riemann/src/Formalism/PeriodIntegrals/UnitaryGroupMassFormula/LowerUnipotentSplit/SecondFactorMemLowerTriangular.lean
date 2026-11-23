import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix

noncomputable section

namespace PI.LowUniSplit

open Formalism.FourierDecayAlt.C2

variable {m : ℕ}

def monoInv (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a i => if i = w a then (d a)⁻¹ else 0

lemma monoInv_mul (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    monoInv w d * monoP w d = 1 := by
  ext a b
  simp only [Matrix.mul_apply, monoInv, monoP, Matrix.of_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp [hd a]
  · have : w a ≠ w b := fun e => h (w.injective e)
    simp [this, h]

lemma monomialMatrix_inv (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (monoP w d)⁻¹ = monoInv w d :=
  Matrix.inv_eq_left_inv (monoInv_mul w d hd)

lemma conj_apply (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((monoP w d)⁻¹ * l * monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by
  rw [monomialMatrix_inv w d hd]
  simp only [Matrix.mul_apply, monoInv, monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq', mul_assoc]

lemma mem_LPg_iff (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ LTset m) :
    l ∈ LPg (monoP w d) ↔ ∀ i j, w.symm i < w.symm j → l i j = 0 := by
  constructor
  · rintro ⟨-, h1, -⟩ i j hij
    have := h1 (w.symm i) (w.symm j) hij
    rw [conj_apply w d hd] at this
    simpa [hd] using this
  · intro h
    refine ⟨hl, fun a b hab => ?_, fun a => ?_⟩
    · rw [conj_apply w d hd]
      have := h (w a) (w b) (by simpa using hab)
      simp [this]
    · rw [conj_apply w d hd, hl.2]
      field_simp [hd a]

lemma mem_Lstg_iff (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ LTset m) :
    l ∈ Lstg (monoP w d) ↔ ∀ i j, w.symm j < w.symm i → l i j = 0 := by
  constructor
  · rintro ⟨-, h1, -⟩ i j hij
    have := h1 (w.symm i) (w.symm j) hij
    rw [conj_apply w d hd] at this
    simpa [hd] using this
  · intro h
    refine ⟨hl, fun a b hab => ?_, fun a => ?_⟩
    · rw [conj_apply w d hd]
      have := h (w a) (w b) (by simpa using hab)
      simp [this]
    · rw [conj_apply w d hd, hl.2]
      field_simp [hd a]

lemma mul_lt_zero {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    {i j : Fin m} (hij : i < j) : (a * b) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [ha.1 i k h, zero_mul]
  · rw [hb.1 k j (lt_of_le_of_lt h hij), mul_zero]

lemma mul_diag {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    (i : Fin m) : (a * b) i i = 1 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [ha.2, hb.2, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb.1 k i h, mul_zero]
    · rw [ha.1 i k h, zero_mul]
  · simp

abbrev Btw (i j : Fin m) : Type := {k : Fin m // j < k ∧ k < i}

lemma mul_below {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    {i j : Fin m} (hji : j < i) :
    (a * b) i j = a i j + b i j + ∑ k : Btw i j, a i k.1 * b k.1 j := by
  rw [Matrix.mul_apply]
  have hpt : ∀ k : Fin m, a i k * b k j =
      (if k = j then a i j else 0) + (if k = i then b i j else 0) +
        (if j < k ∧ k < i then a i k * b k j else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      simp [hb.2, ne_of_lt hji]
    by_cases hki : k = i
    · subst hki
      simp [ha.2, hkj]
    rcases lt_or_gt_of_ne hkj with h1 | h1
    · simp [hkj, hki, hb.1 k j h1, not_lt.mpr h1.le]
    rcases lt_or_gt_of_ne hki with h2 | h2
    · simp [hkj, hki, h1, h2]
    · simp [hkj, hki, ha.1 i k h2, not_lt.mpr h2.le]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun k => by simp) _

variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)

def xs : Fin m → Fin m → ℂ
  | i, j => l i j - ∑ k : Btw i j,
      (if S i k.1 then xs i k.1 else 0) * (if S k.1 j then 0 else xs k.1 j)
termination_by i j => (i : ℕ) - j
decreasing_by
  all_goals
    have h1 := k.2.1
    have h2 := k.2.2
    simp only [Fin.lt_def] at h1 h2
    omega

lemma xs_eq (i j : Fin m) : xs S l i j = l i j - ∑ k : Btw i j,
    (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by
  rw [xs]

def fac1 : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if j < i ∧ S i j then xs S l i j else 0

def fac2 : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if j < i ∧ ¬ S i j then xs S l i j else 0

lemma first_factor_mem_lower_triangular : fac1 S l ∈ LTset m := by
  refine ⟨fun i j h => ?_, fun i => by simp [fac1]⟩
  simp [fac1, ne_of_lt h, not_lt.mpr h.le]

lemma second_factor_mem_lower_triangular : fac2 S l ∈ LTset m := by
  refine ⟨fun i j h => ?_, fun i => by simp [fac2]⟩
  simp [fac2, ne_of_lt h, not_lt.mpr h.le]

lemma fac_mul (hl : l ∈ LTset m) : fac1 S l * fac2 S l = l := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [mul_lt_zero (first_factor_mem_lower_triangular S l) (second_factor_mem_lower_triangular S l) h, hl.1 i j h]
  · subst h; rw [mul_diag (first_factor_mem_lower_triangular S l) (second_factor_mem_lower_triangular S l), hl.2]
  · rw [mul_below (first_factor_mem_lower_triangular S l) (second_factor_mem_lower_triangular S l) h]
    have e : ∀ k : Btw i j, fac1 S l i k.1 * fac2 S l k.1 j =
        (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by
      intro k
      simp [fac1, fac2, ne_of_gt k.2.2, ne_of_gt k.2.1, k.2.1, k.2.2]
    rw [Finset.sum_congr rfl (fun k _ => e k)]
    have : fac1 S l i j + fac2 S l i j = xs S l i j := by
      by_cases hs : S i j <;> simp [fac1, fac2, ne_of_gt h, h, hs]
    rw [this, xs_eq]
    ring

lemma uniq_entries {a b : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    (hsa : ∀ i j, j < i → ¬ S i j → a i j = 0) (hsb : ∀ i j, j < i → S i j → b i j = 0)
    (hab : l = a * b) :
    ∀ n : ℕ, ∀ i j : Fin m, (i : ℕ) - j = n → j < i →
      a i j = (if S i j then xs S l i j else 0) ∧ b i j = (if S i j then 0 else xs S l i j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j hn hji
  have hsum : a i j + b i j = xs S l i j := by
    rw [xs_eq, hab, mul_below ha hb hji, ← hab]
    have e : ∀ k : Btw i j, a i k.1 * b k.1 j =
        (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by
      intro k
      have h1 := k.2.1
      have h2 := k.2.2
      rw [(ih ((i : ℕ) - k.1) (by simp only [Fin.lt_def] at h1 h2; omega) i k.1 rfl h2).1,
        (ih ((k.1 : ℕ) - j) (by simp only [Fin.lt_def] at h1 h2; omega) k.1 j rfl h1).2]
    rw [Finset.sum_congr rfl (fun k _ => e k)]
    ring
  by_cases hs : S i j
  · have := hsb i j hji hs
    simp only [hs, if_true]
    constructor
    · rw [← hsum, this, add_zero]
    · exact this
  · have := hsa i j hji hs
    simp only [hs, if_false]
    constructor
    · exact this
    · rw [← hsum, this, zero_add]

theorem lowSplit : LowSplit := by
  intro m P hP l hl
  obtain ⟨w, d, hd, rfl⟩ := hP
  classical
  let S : Fin m → Fin m → Prop := fun i j => w.symm j < w.symm i
  have hne : ∀ i j : Fin m, i ≠ j → w.symm i ≠ w.symm j := fun i j h e => h (w.symm.injective e)
  refine ⟨(fac1 S l, fac2 S l), ⟨?_, ?_, (fac_mul S l hl).symm⟩, ?_⟩
  · rw [mem_LPg_iff w d hd _ (first_factor_mem_lower_triangular S l)]
    intro i j hij
    have hij' : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : ¬ S i j := not_lt.mpr hij.le
    simp [fac1, hij', this]
  · rw [mem_Lstg_iff w d hd _ (second_factor_mem_lower_triangular S l)]
    intro i j hij
    have hij' : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : S i j := hij
    simp [fac2, hij', this]
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    dsimp only at ha hb hab
    have ha' := (mem_LPg_iff w d hd a ha.1).1 ha
    have hb' := (mem_Lstg_iff w d hd b hb.1).1 hb
    have key := uniq_entries S l ha.1 hb.1
      (fun i j hji hs => ha' i j (lt_of_le_of_ne (not_lt.mp hs) (hne i j (ne_of_gt hji))))
      (fun i j hji hs => hb' i j hs) hab
    have e1 : a = fac1 S l := by
      ext i j
      rcases lt_trichotomy i j with h | h | h
      · rw [ha.1.1 i j h, (first_factor_mem_lower_triangular S l).1 i j h]
      · subst h; rw [ha.1.2, (first_factor_mem_lower_triangular S l).2]
      · rw [(key _ i j rfl h).1]
        by_cases hs : S i j <;> simp [fac1, ne_of_gt h, h, hs]
    have e2 : b = fac2 S l := by
      ext i j
      rcases lt_trichotomy i j with h | h | h
      · rw [hb.1.1 i j h, (second_factor_mem_lower_triangular S l).1 i j h]
      · subst h; rw [hb.1.2, (second_factor_mem_lower_triangular S l).2]
      · rw [(key _ i j rfl h).2]
        by_cases hs : S i j <;> simp [fac2, ne_of_gt h, h, hs]
    rw [e1, e2]

end PI.LowUniSplit
