import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDerivativeSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_line_derivative_schwartz : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ (f : SInf F (Fin a' × Fin (a + a'))) (u : ℝ → SInf F (Fin a' × Fin (a + a'))), (∀ t : ℝ, ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, γ (Multiplicative.ofAdd t)) (pureA F f g) = pureA F (u t) g) → ∃ u₁ : SInf F (Fin a' × Fin (a + a')), Tendsto (fun t : ℝ => t⁻¹ • (u t - u 0)) (𝓝[≠] 0) (𝓝 u₁) := by
  first | exact @GlobalTheory.OrbitArchSlope.orbit_slope_tendsto | exact GlobalTheory.OrbitArchSlope.orbit_slope_tendsto | (intros; apply GlobalTheory.OrbitArchSlope.orbit_slope_tendsto <;> assumption)
