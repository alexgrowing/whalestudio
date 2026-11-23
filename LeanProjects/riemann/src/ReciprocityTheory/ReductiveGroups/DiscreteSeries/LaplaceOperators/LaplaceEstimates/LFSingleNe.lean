import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.BlockEmbeddingSkewHermitian

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

variable {k r : ℕ}

def psiC (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Z : Mat k r) : ℂ :=
  Complex.I / 2 * (LF z c Z - starRingEnd ℂ (LF z c (Hpk k r * Zᴴ * Hpk k r)))

theorem LF_comb (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (s t : ℂ) (X Y : Mat k r) :
    LF z c (s • (X + t • Y)) = s * (LF z c X + t * LF z c Y) := by
  simp only [LF, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun p _ => by ring

theorem parts (Z : Mat k r) :
    let S := Hpk k r * Zᴴ * Hpk k r
    let Y1 := (1 / 2 : ℂ) • (Z + (-1 : ℂ) • S)
    let Y2 := (-Complex.I / 2) • (Z + (1 : ℂ) • S)
    Hpk k r * Y1ᴴ * Hpk k r = -Y1 ∧ Hpk k r * Y2ᴴ * Hpk k r = -Y2 ∧ Z = Y1 + Complex.I • Y2 := by
  intro S Y1 Y2
  have hS : Hpk k r * Sᴴ * Hpk k r = Z := by
    simp only [S, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, ← Matrix.mul_assoc, Hpk_sq,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, Hpk_sq, Matrix.mul_one]
  have hZ : Hpk k r * Zᴴ * Hpk k r = S := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Y1, conjTranspose_smul, conjTranspose_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hS, hZ]
    ext i j; simp; ring
  · simp only [Y2, conjTranspose_smul, conjTranspose_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hS, hZ]
    ext i j; simp; ring
  · ext i j
    simp only [Y1, Y2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (Z i j + S i j) / 2 * Complex.I_mul_I

theorem psiC_parts (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Z S : Mat k r) :
    Complex.I * ((LF z c ((1 / 2 : ℂ) • (Z + (-1 : ℂ) • S))).re : ℂ) +
      Complex.I * (Complex.I * ((LF z c ((-Complex.I / 2) • (Z + (1 : ℂ) • S))).re : ℂ)) =
      Complex.I / 2 * (LF z c Z - starRingEnd ℂ (LF z c S)) := by
  rw [LF_comb, LF_comb]
  apply Complex.ext <;> simp <;> ring

open scoped Matrix.Norms.Operator in
theorem st_mem {Z : Mat k r} (h : Z ∈ levF (levB k r) 0) : Hpk k r * Zᴴ * Hpk k r ∈ levF (levB k r) 0 :=
  isAdjB.mem Z h

theorem nxt_val (p : Fin r) : (nxt k r p).val = if p.val + 1 < r then p.val + 1 else r + k := by
  unfold nxt; split_ifs <;> rfl

theorem LF_single (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (a b : Fin (2 * r + k + 1)) (s : ℂ) :
    LF z c (Matrix.single a b s) =
      ∑ p, if a = eI k r p ∧ b = nxt k r p then c p * (kap k r z p * s) else 0 := by
  refine sum_congr rfl fun p _ => ?_
  rw [Matrix.single_apply]; split_ifs <;> simp

theorem st_single (a b : Fin (2 * r + k + 1)) :
    Hpk k r * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r =
      Matrix.single (flipB k r b) (flipB k r a) (sgnB k r b * sgnB k r a) := by
  ext i j
  rw [mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = flipB k r j ∧ b = flipB k r i
  · obtain ⟨rfl, rfl⟩ := h
    simp [flipB_flipB, sgnB_flip]
  · rw [if_neg h, if_neg, star_zero, mul_zero, zero_mul]
    rintro ⟨rfl, rfl⟩
    exact h ⟨(flipB_flipB a).symm, (flipB_flipB b).symm⟩

def Simple (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Prop :=
  levB k r b = levB k r a + 1 ∧ ¬ (r ≤ a.val ∧ a.val < r + k) ∧ ¬ (r ≤ b.val ∧ b.val < r + k)

theorem simple_of {a b : Fin (2 * r + k + 1)} {p : Fin r} :
    (a = eI k r p ∧ b = nxt k r p → Simple k r a b) ∧
      (flipB k r b = eI k r p ∧ flipB k r a = nxt k r p → Simple k r a b) := by
  have := p.isLt
  have := a.isLt
  have := b.isLt
  simp only [Fin.ext_iff, flipB_val, nxt_val, eI, Simple, levB]
  constructor <;> rintro ⟨h1, h2⟩ <;> split_ifs at h1 h2 ⊢ <;> omega

theorem psiC_zero (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {a b : Fin (2 * r + k + 1)}
    (h : ¬ Simple k r a b) : psiC z c (Matrix.single a b 1) = 0 := by
  rw [psiC, st_single, LF_single, LF_single, sum_eq_zero fun p _ => if_neg fun hp => h (simple_of.1 hp),
    sum_eq_zero fun p _ => if_neg fun hp => h (simple_of.2 hp)]
  simp

theorem LF_single_ne {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} (hc : ∀ p, c p ≠ 0)
    (hT : 0 < Tz k r z) (p : Fin r) {s : ℂ} (hs : s ≠ 0) :
    LF z c (Matrix.single (eI k r p) (nxt k r p) s) ≠ 0 := by
  rw [LF_single, sum_eq_single p (fun q _ hq => if_neg fun h => hq
    (Fin.ext (by have := congrArg Fin.val h.1; exact this.symm))) (by simp), if_pos ⟨rfl, rfl⟩]
  refine mul_ne_zero (hc p) (mul_ne_zero ?_ hs)
  unfold kap
  split_ifs
  · simp
  · exact_mod_cast (Real.sqrt_pos.mpr hT).ne'

theorem psiC_ne {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} (hc : ∀ p, c p ≠ 0) (hT : 0 < Tz k r z)
    {a b : Fin (2 * r + k + 1)} (h : Simple k r a b) : psiC z c (Matrix.single a b 1) ≠ 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have hI : Complex.I / 2 ≠ 0 := div_ne_zero Complex.I_ne_zero two_ne_zero
  rw [psiC, st_single]
  refine mul_ne_zero hI ?_
  unfold Simple levB at h
  by_cases h1 : a.val < r
  · have e1 : a = eI k r ⟨a.val, h1⟩ := rfl
    have e2 : b = nxt k r ⟨a.val, h1⟩ := Fin.ext (by rw [nxt_val]; split_ifs at h ⊢ <;> simp only at * <;> omega)
    rw [LF_single z c (flipB k r b), sum_eq_zero fun p _ => if_neg fun hp => ?_, map_zero, sub_zero]
    · have := LF_single_ne hc hT ⟨a.val, h1⟩ one_ne_zero
      rwa [← e1, ← e2] at this
    · have h2 := congrArg Fin.val hp.2
      have := p.isLt
      rw [flipB_val, nxt_val] at h2
      split_ifs at h2 <;> omega
  · have h3 : r + k ≤ a.val ∧ b.val = a.val + 1 := by split_ifs at h <;> omega
    have hp : 2 * r + k - b.val < r := by omega
    have e1 : flipB k r b = eI k r ⟨_, hp⟩ := Fin.ext (by rw [flipB_val, if_pos (by omega)]; rfl)
    have e2 : flipB k r a = nxt k r ⟨_, hp⟩ := Fin.ext (by
      rw [flipB_val, nxt_val]; split_ifs <;> simp only at * <;> omega)
    rw [LF_single z c a, sum_eq_zero fun p _ => if_neg fun hq => ?_, zero_sub, neg_ne_zero, e1, e2]
    · refine (map_ne_zero _).mpr (LF_single_ne hc hT _ ?_)
      unfold sgnB; split_ifs <;> simp
    · have h2 := congrArg Fin.val hq.1
      have := p.isLt
      simp only [eI] at h2; omega

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
