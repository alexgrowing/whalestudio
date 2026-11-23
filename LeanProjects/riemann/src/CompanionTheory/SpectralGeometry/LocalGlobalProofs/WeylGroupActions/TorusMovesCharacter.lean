import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselSquareIntegrable.SchurHpkAlt
import Formalism.PeriodIntegrals.QuotInv
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Bes

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

def torusTail {r : ℕ} (c : Fin r → ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin r => n ≤ j.val), c j

theorem torusTail_ne {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (n : ℕ) : torusTail c n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => hc j

theorem torusTail_ge {r : ℕ} (c : Fin r → ℂ) {n : ℕ} (hn : r ≤ n) : torusTail c n = 1 := by
  unfold torusTail
  apply Finset.prod_eq_one
  intro j hj
  have := (Finset.mem_filter.1 hj).2
  have := j.isLt
  omega

theorem torusTail_succ {r : ℕ} (c : Fin r → ℂ) (a : Fin r) :
    torusTail c a.val = c a * torusTail c (a.val + 1) := by
  unfold torusTail
  rw [← Finset.prod_insert (a := a) (by simp)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

def torusDiag (k : ℕ) {r : ℕ} (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val ≤ r + k then torusTail c i.val else (star (torusTail c (2 * r + k - i.val)))⁻¹

theorem torusDiag_ne (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0)
    (i : Fin (2 * r + k + 1)) : torusDiag k c i ≠ 0 := by
  unfold torusDiag
  split_ifs
  · exact torusTail_ne hc _
  · exact inv_ne_zero (star_ne_zero.2 (torusTail_ne hc _))

theorem torusDiag_mid (k : ℕ) {r : ℕ} (c : Fin r → ℂ) (i : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : torusDiag k c i = 1 := by
  unfold torusDiag
  rw [if_pos h2, torusTail_ge c h1]

theorem torusDiag_tau (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0)
    (i : Fin (2 * r + k + 1)) : star (torusDiag k c i) * torusDiag k c (tau k r i) = 1 := by
  have hi := i.isLt
  by_cases h1 : i.val < r
  · have e : (tau k r i).val = 2 * r + k - i.val := by
      unfold tau; simp only; rw [if_pos (Or.inl h1)]
    unfold torusDiag
    rw [if_pos (by omega), if_neg (by omega), e,
      show 2 * r + k - (2 * r + k - i.val) = i.val by omega]
    exact mul_inv_cancel₀ (star_ne_zero.2 (torusTail_ne hc _))
  · by_cases h2 : r + k < i.val
    · have e : (tau k r i).val = 2 * r + k - i.val := by
        unfold tau; simp only; rw [if_pos (Or.inr h2)]
      unfold torusDiag
      rw [if_neg (by omega), if_pos (by omega), e, star_inv₀, star_star]
      exact inv_mul_cancel₀ (torusTail_ne hc _)
    · have e : (tau k r i).val = i.val := by
        unfold tau; simp only; rw [if_neg (by omega)]
      rw [torusDiag_mid k c i (by omega) (by omega),
        torusDiag_mid k c (tau k r i) (by omega) (by omega)]
      simp

theorem torusDiag_uh (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    Matrix.diagonal (torusDiag k c) ∈ UH (Hpk k r) := by
  show (Matrix.diagonal (torusDiag k c))ᴴ * Hpk k r * Matrix.diagonal (torusDiag k c) = Hpk k r
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, hpk_row]
  split_ifs with h
  · subst h
    have := torusDiag_tau k hc i
    simp only [Pi.star_apply]
    linear_combination (sgn k r i) * this
  · simp

theorem torus_diagonal_inv {n : ℕ} {d : Fin n → ℂ} (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hd i)

theorem torus_col_conj {k r : ℕ} {d e : Fin (2 * r + k + 1) → ℂ} (hde : ∀ i, d i * e i = 1)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : col k r m) :
    col k r (Matrix.diagonal d * m * Matrix.diagonal e) := by
  intro i j hj hi
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hm i j hj hi]
  split_ifs with h
  · subst h
    rw [mul_one, hde]
  · simp

theorem torus_moves_character :
    ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ a, c a ≠ 0) → ∃ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, a * h = h * a) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, a * m * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ a⁻¹ * m * a ∈ Formalism.QuantumDeterminants.Nset k r ∧ PI.BesselL2FixAtZero.psiGen k r z (fun _ => 1) (a * m * a⁻¹) = PI.BesselL2FixAtZero.psiGen k r z c m) := by
  intro k r z c hz hc
  have hU := torusDiag_uh k hc
  have hd := torusDiag_ne k hc
  refine ⟨Matrix.diagonal (torusDiag k c), hU, fun h hh => ?_, fun m hm => ⟨?_, ?_, ?_⟩⟩
  · have hb := uw_block hh
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hb.2 i j hi]
      split_ifs with e
      · subst e; ring
      · simp
    · by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hb.1 i j hj]
        split_ifs with e
        · subst e; ring
        · simp
      · rw [torusDiag_mid k c i (by omega) (by omega), torusDiag_mid k c j (by omega) (by omega)]
        ring
  · have hm' := (nset_iff m).1 hm
    refine (nset_iff _).2 ⟨uh_mul (uh_mul hU hm'.1) (uh_inv hU), ?_⟩
    rw [torus_diagonal_inv hd]
    exact torus_col_conj (fun i => mul_inv_cancel₀ (hd i)) hm'.2
  · have hm' := (nset_iff m).1 hm
    refine (nset_iff _).2 ⟨uh_mul (uh_mul (uh_inv hU) hm'.1) hU, ?_⟩
    rw [torus_diagonal_inv hd]
    exact torus_col_conj (fun i => inv_mul_cancel₀ (hd i)) hm'.2
  · unfold PI.BesselL2FixAtZero.psiGen
    congr 4
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.isLt
    have he : torusDiag k c (eI k r a) = c a * torusTail c (a.val + 1) := by
      unfold torusDiag
      rw [if_pos (by simp only [eI]; omega)]
      exact torusTail_succ c a
    beta_reduce
    rw [one_mul, torus_diagonal_inv hd]
    unfold PI.BesselL2FixAtZero.ellA
    split_ifs with h
    · have he' : torusDiag k c (eI k r ⟨a.val + 1, h⟩) = torusTail c (a.val + 1) := by
        unfold torusDiag
        rw [if_pos (by simp only [eI]; omega)]
        rfl
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, he, he']
      have := torusTail_ne hc (a.val + 1)
      field_simp
    · have hzz : Matrix.diagonal (fun i => (torusDiag k c i)⁻¹) *ᵥ z = z := by
        funext i
        rw [Matrix.mulVec_diagonal]
        by_cases hi : i.val < r ∨ r + k < i.val
        · rw [hz i hi, mul_zero]
        · rw [torusDiag_mid k c i (by omega) (by omega), inv_one, one_mul]
      rw [← Matrix.mulVec_mulVec, hzz, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, he,
        torusTail_ge c (by omega), mul_one]

end GlobalTheory.CompanionTheory.Bes
