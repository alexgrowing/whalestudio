import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitKoszulInvariantOfFiniteClosedFibreZeros
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
theorem _root_.GlobalTheory.T.isUnit_koszulInvariant_of_finite_closedFibre_zeros : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℚ O] (F : Type) [Field F] (f : O →+* F) (x : KeyIn O) (xF : KeyIn F) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : xF.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sF : Fin xF.P.g → RR xF n) (κ : Fˣ) (a : O) (e : ℤ), Function.Injective f → admitted x.P.g n l l' al → KeyVia xF x f φ w → (∀ i, SecVia xF x φ w (sF i) (s (i.cast hg))) → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → KaVal xF n l l' al sF κ → (κ : F) ^ e = f a → e ≠ 0 → IsUnit a := by
  first | exact @GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros | exact GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros | (intros; apply GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros <;> assumption)
