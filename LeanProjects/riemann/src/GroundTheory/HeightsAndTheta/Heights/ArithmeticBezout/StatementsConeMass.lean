import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMassOfFibre.Statement : Prop :=
  ∀ (n m δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsProjPrime J →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = δ) →
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
        (δ : ENNReal) * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}

theorem ConeMassOfFibre.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w = ((1 : ℕ) : ℕ∞) := by
  refine ⟨isProjPrime_point ℂ, ?_⟩
  have hnull : ∀ᵐ π : Fin 1 → Fin 1 → ℂ, π 0 0 ≠ 0 := by
    have hp : MeasurePreserving (fun π : Fin 1 → Fin 1 → ℂ => π 0 0) :=
      (volume_preserving_funUnique (Fin 1) ℂ).comp
        (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))
    rw [ae_iff]
    have hset : {π : Fin 1 → Fin 1 → ℂ | ¬ π 0 0 ≠ 0} = (fun π => π 0 0) ⁻¹' {0} := by
      ext π; simp
    rw [hset, hp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
    simp
  filter_upwards [hnull] with π hπ
  refine Filter.Eventually.of_forall fun w => ?_
  have hfib : {y | y ∈ coneSet (HermNorm.std 1) ⊥ ∧ linProj π y = w} =
      {WithLp.toLp 2 fun _ => w 0 / π 0 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, coneSet, Ideal.mem_bot]
    constructor
    · rintro ⟨-, hy⟩
      have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v 0) hy
      simp only [linProj, Fin.sum_univ_one] at h0
      ext i
      fin_cases i
      simp only [Fin.zero_eta, Fin.isValue]
      rw [← h0]
      field_simp
    · rintro rfl
      refine ⟨fun q hq => by simp [hq], ?_⟩
      ext i
      fin_cases i
      simp [linProj]
      field_simp
  rw [fibreCount, hfib, Set.encard_singleton]
  rfl

end

end GroundTheory.Heights₂.Heights
