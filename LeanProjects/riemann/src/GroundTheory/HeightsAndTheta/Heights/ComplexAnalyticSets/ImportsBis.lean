import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

def LogIntegrableOn.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (u : Fin n → ℂ) (B : Set (Fin n → ℂ)),
    IsAffVariety J d → IsFiniteProj J A → (∀ i, SmoothNear (zeroLocus J) (φ i)) →
    linForm u ∉ J → MeasurableSet B → Bornology.IsBounded B →
      ProjIntegrable J A (B.indicator fun x => Real.log ‖linVal u x‖) φ

theorem LogIntegrableOn.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 ∧
      IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      (∀ i : Fin 1, SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)))
        ((fun _ x => ‖x 0‖ ^ 2 : Fin 1 → (Fin 1 → ℂ) → ℝ) i)) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      MeasurableSet (Metric.ball (0 : Fin 1 → ℂ) 1) ∧
      Bornology.IsBounded (Metric.ball (0 : Fin 1 → ℂ) 1) :=
  ⟨isAffVariety_bot 1, isFiniteProj_one 1, fun _ => smoothNear_of_contDiff _ contDiff_normSq_coord,
    linForm_one_not_mem_point ℂ, measurableSet_ball, Metric.isBounded_ball⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
