import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DedekindZetaFactorizationRay
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_zeta_factorization_ray : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  first | exact @GlobalTheory.Mem.ray_prod_LSeries_nonneg | exact GlobalTheory.Mem.ray_prod_LSeries_nonneg | (intros; apply GlobalTheory.Mem.ray_prod_LSeries_nonneg <;> assumption)
