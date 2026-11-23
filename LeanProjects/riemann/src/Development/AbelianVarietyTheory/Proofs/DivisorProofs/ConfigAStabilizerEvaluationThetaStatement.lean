import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerEvaluationTheta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_stabilizer_evaluation_theta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ N : ℕ, ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ k ∈ K, ∀ l : (AE F E)ˣ,
        ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ))))‖ₑ ∂G₁.M.μ ≤
          C * GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
  first | exact @GlobalTheory.XTermBound.bound | exact GlobalTheory.XTermBound.bound | (intros; apply GlobalTheory.XTermBound.bound <;> assumption)
