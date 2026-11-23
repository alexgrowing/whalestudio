import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_section_extends_normal : ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z] (AA : LB Z), AA.IsLB → (∀ z : Z, ∃ (d : ℕ) (s : H0 AA d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp (FractionRing R) ⟶ Z) (e : LB.Gen (AA.pull x)), e.IsGen → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∃ χ : Sp W ⟶ Z, spMap gam ≫ x = jK W ≫ χ ∧ ∃ e' : LB.Gen (AA.pull χ), e'.IsGen ∧ ∀ z J, Good AA z J → val (L := AA) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J = val (L := AA) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (jK W) z J) → ∃ χ : Sp R ⟶ Z, jK R ≫ χ = x := by
  first | exact @GlobalTheory.ExtLB.exists_extension | exact GlobalTheory.ExtLB.exists_extension | (intros; apply GlobalTheory.ExtLB.exists_extension <;> assumption)
