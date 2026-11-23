import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairLineDerivativeTheta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_pair_line_derivative_theta : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ : (Fin a' × Fin (a + a') → AF F) → ℂ, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∃ (m : ℕ) (φ : Fin m → (Fin a' × Fin (a + a') → Af F) → ℂ) (f : ℝ → Fin m → SInf F (Fin a' × Fin (a + a'))) (f₁ : Fin m → SInf F (Fin a' × Fin (a + a'))), (∀ i, φ i ∈ SB (Fin a' × Fin (a + a') → Af F)) ∧ (∀ t : ℝ, om' (1, γ (Multiplicative.ofAdd t)) Φ = ∑ i, pureA F (f t i) (φ i)) ∧ Φ₁ = ∑ i, pureA F (f₁ i) (φ i) ∧ ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (f t i - f 0 i)) (𝓝[≠] 0) (𝓝 (f₁ i)) := by
  first | exact @GlobalTheory.ThetaOrbit.orbit | exact GlobalTheory.ThetaOrbit.orbit | (intros; apply GlobalTheory.ThetaOrbit.orbit <;> assumption)
