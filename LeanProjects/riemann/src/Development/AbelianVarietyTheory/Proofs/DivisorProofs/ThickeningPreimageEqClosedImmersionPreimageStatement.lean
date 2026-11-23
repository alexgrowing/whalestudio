import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningPreimageEqClosedImmersionPreimage
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_preimage_eq_closedImmersion_preimage : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0}) (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y), (∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e) → ∀ (V : G'.left.Opens) (W : Y.Opens), φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V → ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V := by
  first | exact @GlobalTheory.Mum.thick_preimage_eq | exact GlobalTheory.Mum.thick_preimage_eq | (intros; apply GlobalTheory.Mum.thick_preimage_eq <;> assumption)
