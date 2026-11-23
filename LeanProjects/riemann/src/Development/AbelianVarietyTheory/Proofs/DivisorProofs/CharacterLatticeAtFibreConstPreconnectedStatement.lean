import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterLatticeAtFibre_const_preconnected : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  first | exact @GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | exact GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | (intros; apply GlobalTheory.UPoinc.GFib.latAt_const_on_fibre <;> assumption)
