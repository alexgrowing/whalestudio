import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarLelongAnnulus
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLogDensNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

namespace LelongNumberMonotone

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem maDens_logDistSq_nonneg (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (hzx : z ≠ x)
    (hs : IsSheetAt J A z s) :
    0 ≤ ReciprocityTheory.AnForm.maDens (fun _ : Fin (d + 1) => logDistSq x ∘ s) (A *ᵥ z) := by
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
    RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

theorem chartDens_annulus_nonneg (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := maDens_logDistSq_nonneg x z h.choose (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end LelongNumberMonotone

open LelongNumberMonotone in

theorem VarLelongMono.proof (hA : VarLelongAnnulus.Statement) : VarLelongMono.Statement := by
  intro n d J A x r s hJ hdim hAf hr hrs
  have heq := hA n d J A x r s hJ hdim hAf hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg x hr y
  have hrs0 : 0 ≤ r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
