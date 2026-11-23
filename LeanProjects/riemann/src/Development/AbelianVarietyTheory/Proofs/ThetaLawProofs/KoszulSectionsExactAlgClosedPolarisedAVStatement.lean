import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAV
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
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
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  first | exact @GlobalTheory.koszul_sections_exact_field | exact GlobalTheory.koszul_sections_exact_field | (intros; apply GlobalTheory.koszul_sections_exact_field <;> assumption)
