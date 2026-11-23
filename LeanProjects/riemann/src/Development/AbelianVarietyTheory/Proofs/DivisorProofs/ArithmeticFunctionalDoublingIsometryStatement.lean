import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalDoublingIsometry
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
theorem _root_.GlobalTheory.T.arithmetic_functional_doubling_isometry : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X B : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : B ⟶ Sp k) (π : X ⟶ B) (hπ : π ≫ q = p) (g : ℕ), IsArithVar p (g + 1) → ∀ (f : X ⟶ X) (hf : f ≫ p = p), f ≫ π = π → f (genericPoint X) = genericPoint X → f.residueDegree (genericPoint X) = 4 ^ g → ∀ (L : HermLB p) (N N' : HermLB q), (L.pull f hf).Isometric (L.pow 4) → ∀ Φ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ, IsArFun ![L, N.pull π hπ, N'.pull π hπ] (g + 1) Φ → Φ (MvPolynomial.X 0 ^ (g + 1) * MvPolynomial.X 2) = 0 ∧ Φ (MvPolynomial.X 0 ^ (g + 2)) = 0 ∧ Φ (MvPolynomial.X 0 ^ (g + 1) * MvPolynomial.X 1) = 0 := by
  first | exact @GlobalTheory.ThetaRR.arFun_vanish_of_quartic | exact GlobalTheory.ThetaRR.arFun_vanish_of_quartic | (intros; apply GlobalTheory.ThetaRR.arFun_vanish_of_quartic <;> assumption)
