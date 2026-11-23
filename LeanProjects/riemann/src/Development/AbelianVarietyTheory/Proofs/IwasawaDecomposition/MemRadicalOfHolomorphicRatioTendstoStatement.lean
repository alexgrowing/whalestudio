import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_radical_of_holomorphic_ratio_tendsto : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  first | exact @GlobalTheory.ShFam.BdArc.exists_eq_mul_pow_of_tendsto_zero | exact GlobalTheory.ShFam.BdArc.exists_eq_mul_pow_of_tendsto_zero | (intros; apply GlobalTheory.ShFam.BdArc.exists_eq_mul_pow_of_tendsto_zero <;> assumption)
