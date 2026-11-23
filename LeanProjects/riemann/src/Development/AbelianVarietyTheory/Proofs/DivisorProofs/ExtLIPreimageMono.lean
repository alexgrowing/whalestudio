import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extLI_preimage_le {X X' Y : Scheme.{0}} (a : Y ⟶ X') (f : X' ⟶ X) (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X.Opens) : a ⁻¹ᵁ (f ⁻¹ᵁ W) ≤ α ⁻¹ᵁ W := by
  intro y hy
  show α y ∈ W
  rw [← e, Scheme.Hom.comp_apply]
  exact hy

theorem extLI_le_chart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X'.Opens) (j : L.ι) (hW : W ≤ f ⁻¹ᵁ L.U j) :
    a ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => extLI_preimage_le a f α e (L.U j) (hW hy)

theorem extLI_le_wchart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (j : Fin 1 → L.ι) :
    a ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j ≤ LB.wchart L (K := Fin 1) (fun _ => α) j :=
  fun _ hy => Set.mem_iInter.2 fun k => extLI_preimage_le a f α e (L.U (j k)) (Set.mem_iInter.1 hy k)

theorem extLI_preimage_mono {X Y : Scheme.{0}} (a : Y ⟶ X) {V V' : X.Opens} (hV : V ≤ V') : a ⁻¹ᵁ V ≤ a ⁻¹ᵁ V' :=
  fun _ hz => hV hz

theorem extLI_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE h3).op).hom x := by
  change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.Mum
