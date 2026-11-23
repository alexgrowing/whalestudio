import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Pinch

theorem gm_id_val_germ {X : Scheme.{0}} (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)ˣ) :
    (gm (𝟙 X) x U a).val = (X.presheaf.germ U x h).hom a.val := by
  rw [gm_val (𝟙 X) x U h]
  rfl

theorem isUnit_res_basicOpen' {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) :
    IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) :=
  X.toRingedSpace.isUnit_res_basicOpen e

def basicUnit {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) : Γ(X, X.basicOpen e)ˣ :=
  (isUnit_res_basicOpen' e).unit

theorem gm_basicUnit_val {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) (x : X) (hx : x ∈ X.basicOpen e) :
    (gm (𝟙 X) x _ (basicUnit e)).val = (X.presheaf.germ D x (X.basicOpen_le e hx)).hom e := by
  rw [gm_id_val_germ x _ hx]
  show (X.presheaf.germ (X.basicOpen e) x hx).hom ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) = _
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx e

theorem exists_locGen_of_secFam : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (J : Type) (D : J → X.Opens) (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)), GlobalTheory.Pinch.IsSecFam L D k hD e → ∃ (V : X.Opens) (a : ∀ i, Γ(X, V ⊓ L.U i)ˣ), (∀ j (x : X) (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) → x ∈ V) ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL J D k hD e he
  let B : J → X.Opens := fun j => X.basicOpen (e j)
  have hB : ∀ j, B j ≤ D j := fun j => X.basicOpen_le (e j)
  let V : X.Opens := ⨆ j, B j
  have hBV : ∀ j, B j ≤ V := fun j => le_iSup B j

  have ge : ∀ j j' (z : X) (hz : z ∈ B j) (hz' : z ∈ B j'),
      gm (𝟙 X) z (B j) (basicUnit (e j)) =
        gm (𝟙 X) z (L.U (k j) ⊓ L.U (k j')) (L.g (k j) (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro j j' z hz hz'
    apply Units.ext
    rw [Units.val_mul, gm_basicUnit_val _ z hz, gm_basicUnit_val _ z hz',
      gm_id_val_germ z (L.U (k j) ⊓ L.U (k j')) ⟨hD j (hB j hz), hD j' (hB j' hz')⟩]
    exact he j j' z (hB j hz) (hB j' hz')
  let W : L.ι → J → X.Opens := fun i j => B j ⊓ L.U i
  have hWV : ∀ i j, W i j ≤ V ⊓ L.U i := fun i j => inf_le_inf_right _ (hBV j)
  have hWg : ∀ i j, W i j ≤ L.U i ⊓ L.U (k j) := fun i j z hz => ⟨hz.2, hD j (hB j hz.1)⟩
  have hWB : ∀ i j, W i j ≤ B j := fun i j => inf_le_left
  let u : ∀ i j, Γ(X, W i j)ˣ := fun i j => res (hWg i j) (L.g i (k j)) * res (hWB i j) (basicUnit (e j))
  have gu : ∀ i j (z : X) (hz : z ∈ W i j), gm (𝟙 X) z (W i j) (u i j) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) := by
    intro i j z hz
    simp only [u, map_mul]
    rw [gm_res _ z (hWg i j) hz, gm_res _ z (hWB i j) hz]
  have key : ∀ i j j' (z : X), z ∈ L.U i → z ∈ B j → z ∈ B j' →
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j')) (L.g i (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro i j j' z hi hj hj'
    rw [ge j j' z hj hj', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) z hi (hD j (hB j hj)) (hD j' (hB j' hj'))]
  have glued : ∀ i, ∃ s : Γ(X, V ⊓ L.U i)ˣ, ∀ j, res (hWV i j) s = u i j := by
    intro i
    refine glue_unit (V ⊓ L.U i) (W i) (hWV i) (fun z hz => ?_) (u i) (fun j j' z hz => ?_)
    · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj, hz.2⟩
    · rw [gu i j z hz.1, gu i j' z hz.2]
      exact key i j j' z hz.1.2 hz.1.1 hz.2.1
  choose a ha using glued
  refine ⟨V, a, fun j x hx hu => hBV j ((Scheme.mem_basicOpen X (e j) x hx).2 hu), ?_⟩
  intro y i i' hy hi hi'
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have ga : ∀ i (hi : y ∈ L.U i), gm (𝟙 X) y (V ⊓ L.U i) (a i) =
      gm (𝟙 X) y (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) y (B j) (basicUnit (e j)) := by
    intro i hi
    rw [← gm_res _ y (hWV i j) ⟨hj, hi⟩, ha i j]
    exact gu i j y ⟨hj, hi⟩
  rw [ga i hi, ga i' hi', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) y hi hi' (hD j (hB j hj))]

end GlobalTheory.Pinch
