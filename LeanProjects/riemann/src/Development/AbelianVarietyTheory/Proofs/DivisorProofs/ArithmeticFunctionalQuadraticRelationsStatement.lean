import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelations
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_functional_quadratic_relations : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsIntegral S] (p : S ⟶ Sp k), IsRegSurf p → ∀ (M D : HermLB p) (t I a ρ : ℝ), (∀ (N : HermLB p) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ), IsArFun ![M, D, N] 1 Ψ → Ψ (MvPolynomial.X 0 * MvPolynomial.X 2) - t * gdeg N 1 / 2 = -(Ψ (MvPolynomial.X 1 * MvPolynomial.X 2) / 2) ∧ Ψ (MvPolynomial.X 0 ^ 2) / 2 - I / 2 = Ψ (MvPolynomial.X 1 ^ 2) / 8 - a / 12 + ρ / 2 * gdeg D 1) → a = 6 * I + (6 * ρ + 3 * t) * gdeg D 1 := by
  first | exact @GlobalTheory.ThetaRR.Elim.elim | exact GlobalTheory.ThetaRR.Elim.elim | (intros; apply GlobalTheory.ThetaRR.Elim.elim <;> assumption)
