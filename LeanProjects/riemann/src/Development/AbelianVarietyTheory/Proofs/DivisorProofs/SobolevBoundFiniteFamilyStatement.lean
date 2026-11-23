import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundFiniteFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_bound_finite_family : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G₁ : Geo σ b a')
    (X : Chars F E) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G₁ X om₁ om₁' →
    ∀ (m : ℕ) (φ : Fin m → (Fin b × Fin (b + a') → Af F) → ℂ), (∀ j, φ j ∈ SB _) →
    ∃ (s : Finset (ℕ × ℕ)) (C : ENNReal), C ≠ ⊤ ∧ ∀ f : Fin m → SInf F (Fin b × Fin (b + a')),
      ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (∑ j, pureA F (f j) (φ j)))‖ₑ ∂G₁.M.μ ≤
        C * ∑ j, ENNReal.ofReal ((s.sup (schwartzSeminormFamily ℂ _ ℂ)) (f j)) := by
  first | exact @GlobalTheory.WeilSeminorm.lintegral_thetaSum_le | exact GlobalTheory.WeilSeminorm.lintegral_thetaSum_le | (intros; apply GlobalTheory.WeilSeminorm.lintegral_thetaSum_le <;> assumption)
