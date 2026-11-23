import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXy
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ), M.Ok → Ell M.L φ → ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ), (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧ ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  first | exact @GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | exact GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | (intros; apply GlobalTheory.EllipticModel.exists_mul_prod_eq_xy <;> assumption)
