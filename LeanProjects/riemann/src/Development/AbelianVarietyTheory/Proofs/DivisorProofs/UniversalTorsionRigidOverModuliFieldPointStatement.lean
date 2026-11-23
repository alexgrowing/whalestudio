import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTorsionRigidOverModuliFieldPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_torsion_rigid_over_moduli_fieldPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K L : Type) [Field K] [Field L] (y : Sp K ⟶ Xo.XF c) (x : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∀ κ₁ κ₂ : Sp L ⟶ Sp K, κ₁ ≫ y = κ₂ ≫ y → κ₁ ≫ x.left = κ₂ ≫ x.left := by
  first | exact @GlobalTheory.TorsRigid.torsion_rigid | exact GlobalTheory.TorsRigid.torsion_rigid | (intros; apply GlobalTheory.TorsRigid.torsion_rigid <;> assumption)
