import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.UnitaryMatrixCoefficientDecay
import GroundTheory.AutomorphicForms.HilbertSchmidtCompact
import GroundTheory.AutomorphicForms.CompactSelfAdjoint

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgHeA

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_smul_rep {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (b : H) :
    Integrable (fun g => f g • τ g b) ν := by
  refine (hf.norm.mul_const ‖b‖).mono' (hf.aestronglyMeasurable.smul (hτ.4 b).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_smul, hτ.norm]

theorem integrable_mul_inner {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (a b : H) :
    Integrable (fun g => f g * ⟪a, τ g b⟫_ℂ) ν := by
  refine (hf.norm.mul_const (‖a‖ * ‖b‖)).mono'
    (hf.aestronglyMeasurable.mul (continuous_const.inner (hτ.4 b)).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖⟪a, τ g b⟫_ℂ‖ ≤ ‖a‖ * ‖τ g b‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖b‖ := by rw [hτ.norm]

def coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => ∫ g, f g • τ g b ∂ν
      map_add' := fun x y => by
        rw [← integral_add (integrable_smul_rep hτ hf x) (integrable_smul_rep hτ hf y)]
        simp only [map_add, smul_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        simp only [map_smul, smul_comm c] }
    (∫ g, ‖f g‖ ∂ν) fun b => by
      refine (norm_integral_le_of_norm_le (hf.norm.mul_const ‖b‖) (.of_forall fun g => ?_)).trans_eq ?_
      · rw [norm_smul, hτ.norm]
      · rw [integral_mul_const]

theorem coefOp_apply (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (b : H) :
    coefOp ν τ hτ f hf b = ∫ g, f g • τ g b ∂ν := rfl

theorem inner_coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (a b : H) :
    ⟪a, coefOp ν τ hτ f hf b⟫_ℂ = ∫ g, f g * ⟪a, τ g b⟫_ℂ ∂ν := by
  rw [coefOp_apply, ← integral_inner (integrable_smul_rep hτ hf b)]
  simp only [inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
