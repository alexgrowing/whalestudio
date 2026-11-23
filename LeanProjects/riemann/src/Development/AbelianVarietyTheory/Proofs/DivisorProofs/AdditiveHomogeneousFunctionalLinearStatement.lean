import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousFunctionalLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_homogeneous_functional_linear : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ L : Fn F n d → ℂ, (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d), L (Ψ + Ψ') = L Ψ + L Ψ') →
      (∀ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), L (c • Ψ) = c * L Ψ) →
      (∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ,
        ∀ f : SInf F (Fin n × Fin d), L (pureA F f g) = T f) →
      (∀ x : Matrix (Fin n) (Fin d) E, ∀ Ψ ∈ schA F (Fin n × Fin d), L (M.co.rho B.ψ (incM F x) Ψ) = L Ψ) →
      ∃ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), L Ψ = c * thetaSum F Ψ := by
  first | exact @GlobalTheory.ThetaUniq.unique_of_ratInv | exact GlobalTheory.ThetaUniq.unique_of_ratInv | (intros; apply GlobalTheory.ThetaUniq.unique_of_ratInv <;> assumption)
