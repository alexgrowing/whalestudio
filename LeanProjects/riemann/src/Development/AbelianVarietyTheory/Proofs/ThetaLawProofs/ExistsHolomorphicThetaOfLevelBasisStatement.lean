import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicThetaOfLevelBasis
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_theta_of_level_basis : Out.Laws → ThetaUnifAV → ∀ (g m : ℕ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ), charHalf g a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → LevBasis a b m Th → ∃ lam : (Fin g → Fin g → ℂ) → ℂ, DifferentiableOn ℂ lam (Key.phDom g) ∧ ∀ p ∈ Key.phDom g, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (bs : Fin (m ^ x.P.g) → RR x m) (la : ℂˣ), Wit x h u (per p) a b → (∀ k, FnPw x u (bs k) (Th (k.cast (by rw [h])) p)) → IsSquareDeterminantComparison x m al bs la → (la : ℂ) = lam p := by
  first | exact @GlobalTheory.SimilTheta.l2Val_holomorphic | exact GlobalTheory.SimilTheta.l2Val_holomorphic | (intros; apply GlobalTheory.SimilTheta.l2Val_holomorphic <;> assumption)
