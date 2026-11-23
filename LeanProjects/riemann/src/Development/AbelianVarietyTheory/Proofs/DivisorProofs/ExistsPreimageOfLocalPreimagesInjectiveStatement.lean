import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_of_local_preimages_injective : ∀ {X Y : Scheme.{0}} (a : Y ⟶ X), (∀ U : X.Opens, Function.Injective (a.app U).hom) → ∀ (V : X.Opens) {B : Type} (W : B → X.Opens), V ≤ ⨆ b, W b → ∀ (x : Γ(Y, a ⁻¹ᵁ V)), (∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) → ∃ y : Γ(X, V), (a.app V).hom y = x := by
  first | exact @GlobalTheory.Mum.imgLoc_exists | exact GlobalTheory.Mum.imgLoc_exists | (intros; apply GlobalTheory.Mum.imgLoc_exists <;> assumption)
