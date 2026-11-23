import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairThetaUniformBoundFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_theta_uniform_bound_family : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (χY χW : Chr F E) (om : Rep σ Y W) (r s r' s' : ℕ), IsPair B M χY χW om r s r' s' → ∀ (m : ℕ) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ) (f : ℝ → Fin m → SInf F (Fin n × Fin d)) (f₁ : Fin m → SInf F (Fin n × Fin d)), (∀ i, φ i ∈ SB (Fin n × Fin d → Af F)) → (∀ i, Tendsto (fun t : ℝ => t⁻¹ • (f t i - f 0 i)) (𝓝[≠] 0) (𝓝 (f₁ i))) → ∀ g h, HasDerivAt (fun t : ℝ => theta om (∑ i, pureA F (f t i) (φ i)) g h) (theta om (∑ i, pureA F (f₁ i) (φ i)) g h) 0 := by
  first | exact @GlobalTheory.ThetaKernelDeriv.hasDerivAt_theta_sum | exact GlobalTheory.ThetaKernelDeriv.hasDerivAt_theta_sum | (intros; apply GlobalTheory.ThetaKernelDeriv.hasDerivAt_theta_sum <;> assumption)
