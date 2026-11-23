import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VeryAmpleByDescendsCountableSubring
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
theorem _root_.GlobalTheory.T.veryAmpleBy_descends_to_countable_subring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Flat f] (H : LB X) (m : ℕ) (s : Fin (m + 1) → H.Sec) (S : Set R), H.IsLB → VeryAmpleBy f H s → S.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) (H₀ : LB X₀) (s₀ : Fin (m + 1) → H₀.Sec), Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R ∧ IsPullback π f f₀ (spMap R₀.subtype) ∧ Flat f₀ ∧ H₀.IsLB ∧ VeryAmpleBy f₀ H₀ s₀ ∧ LBIso H (H₀.pull π) := by
  first | exact @GlobalTheory.veryAmpleBy_descends_countable_subring | exact GlobalTheory.veryAmpleBy_descends_countable_subring | (intros; apply GlobalTheory.veryAmpleBy_descends_countable_subring <;> assumption)
