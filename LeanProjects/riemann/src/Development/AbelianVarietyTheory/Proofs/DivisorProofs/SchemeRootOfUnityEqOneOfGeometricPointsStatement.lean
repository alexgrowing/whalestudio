import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_rootOfUnity_eq_one_of_geometric_points : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ) (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  first | exact @GlobalTheory.rootOfUnity_eq_one_of_geom | exact GlobalTheory.rootOfUnity_eq_one_of_geom | (intros; apply GlobalTheory.rootOfUnity_eq_one_of_geom <;> assumption)
