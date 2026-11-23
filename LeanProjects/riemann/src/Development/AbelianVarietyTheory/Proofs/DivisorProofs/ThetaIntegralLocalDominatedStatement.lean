import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLocalDominated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_local_dominated : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ ∈ schA F (Fin a × Fin (a + a')), ∀ h₀ : UA σ G.W.J, ∃ U ∈ 𝓝 h₀, ∃ bound : UA σ G.V.J → ℝ,
      IntegrableOn bound G.M.dom G.M.μ ∧ ∀ h ∈ U, ∀ᵐ g ∂(G.M.μ.restrict G.M.dom), ‖theta om Φ g h‖ ≤ bound g := by
  first | exact @GlobalTheory.ThetaDom.theta_dominated | exact GlobalTheory.ThetaDom.theta_dominated | (intros; apply GlobalTheory.ThetaDom.theta_dominated <;> assumption)
