import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantEqOfIndependentGenericTuples
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
theorem _root_.GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples : Out.Laws → ∀ (k K : Type) [Field k] [CharZero k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T T' : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s s' : Fin x'.P.g → RR x' n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k (Sum.elim T T') → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → (∀ i, Coords x' b' (fun j => T' (i, j)) (s' i).f) → KaVal x' n l l' al s κ → KaVal x' n l l' al s' κ' → κ = κ' := by
  first | exact @GlobalTheory.KeyGeneric.kaVal_eq_of_generic | exact GlobalTheory.KeyGeneric.kaVal_eq_of_generic | (intros; apply GlobalTheory.KeyGeneric.kaVal_eq_of_generic <;> assumption)
