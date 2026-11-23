import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyBoundedUniformly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_family_bounded_uniformly : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (T : Type) (Ψ : T → Fn F n d), (∀ t, Ψ t ∈ M.So B.ψ B.τ₁) →
    (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) →
    ∃ k : ℕ, ∀ w : T → ℝ, (∀ t, 0 ≤ w t) → (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ C : ℝ, ∀ t, w t * ‖l (Ψ t)‖ ≤ C) →
      ∃ C : ℝ, ∀ t g h, w t * ‖theta om (Ψ t) g h‖ ≤ C * (ht h : ℝ) ^ k := by
  first | exact @GlobalTheory.ThetaUnifWeight.theta_unif_weight | exact GlobalTheory.ThetaUnifWeight.theta_unif_weight | (intros; apply GlobalTheory.ThetaUnifWeight.theta_unif_weight <;> assumption)
