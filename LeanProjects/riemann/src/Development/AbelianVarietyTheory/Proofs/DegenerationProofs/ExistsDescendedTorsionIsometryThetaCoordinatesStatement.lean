import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescendedTorsionIsometryThetaCoordinates
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_torsion_isometry_theta_coordinates : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  first | exact @GlobalTheory.DescendIso.exists_descend | exact GlobalTheory.DescendIso.exists_descend | (intros; apply GlobalTheory.DescendIso.exists_descend <;> assumption)
