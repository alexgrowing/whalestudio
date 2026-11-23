import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantIndependentOfSections
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
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
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyInvariant_independent_of_sections : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted x.P.g n l l' al → ∃ κ : Kˣ, (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧ ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (φ : _) (w : _) (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyVia x' x f φ w ∧ KaVal x' n l l' al s' κ' := by
  first | exact @GlobalTheory.KaIndep.kaVal_independent | exact GlobalTheory.KaIndep.kaVal_independent | (intros; apply GlobalTheory.KaIndep.kaVal_independent <;> assumption)
