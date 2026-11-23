import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulInvariantLocallyHolomorphicPeriodMatrix
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
theorem _root_.GlobalTheory.T.koszulInvariant_locally_holomorphic_periodMatrix : Out.Laws → ThetaUnifAV → ∀ (g : ℕ) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (a b : Fin g → ℂ) (p₀ : (Fin g → Fin g → ℂ)) (x₀ : KeyIn ℂ) (h₀ : x₀.P.g = g) (u₀ : HolUnif x₀.P.A x₀.P.L g) (s₀ : Fin x₀.P.g → RR x₀ n) (κ₀ : ℂˣ), charHalf g a b → admitted g n l l' al → p₀ ∈ Key.phDom g → Wit x₀ h₀ u₀ (per p₀) a b → KaVal x₀ n l l' al s₀ κ₀ → ∃ (W : Set (Fin g → Fin g → ℂ)) (V : (Fin g → Fin g → ℂ) → ℂ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ Key.phDom g ∧ DifferentiableOn ℂ V W ∧ ∀ p ∈ W, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g), Wit x h u (per p) a b → ∃ (s : Fin x.P.g → RR x n) (κ : ℂˣ), KaVal x n l l' al s κ ∧ (κ : ℂ) = V p := by
  first | exact @GlobalTheory.KeyKa.KaHol.kaVal_locally_holomorphic | exact GlobalTheory.KeyKa.KaHol.kaVal_locally_holomorphic | (intros; apply GlobalTheory.KeyKa.KaHol.kaVal_locally_holomorphic <;> assumption)
