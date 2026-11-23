import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingMumfordLambdaSquare
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLinComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_mumfordLambda_square : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ P.A), x₁ ^ n = 1 → x₂ ^ n = 1 → y₁ ^ n = 1 → y₂ ^ n = 1 → ∀ (c₁ c₂ : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L n x₁ y₂ c₁ → WeilIs P.A P.L n x₂ y₁ c₂ → WeilIs (G2 P.A) (abelian₂ P.A P.L) n (lift x₁ x₂) (lift y₁ y₂) (c₁ * c₂) := by
  first | exact @GlobalTheory.LamPairing.weilIs_lam | exact GlobalTheory.LamPairing.weilIs_lam | (intros; apply GlobalTheory.LamPairing.weilIs_lam <;> assumption)
