import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_map_gs {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (f.stalkMap y).hom (gs (𝟙 X) (f y) U a) := by
  rw [gs_eq f y U h, gs_eq (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

def IsSecOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) : Prop :=
  ∀ (z : X) (k k' : L.ι), z ∈ W → z ∈ L.U k → z ∈ L.U k' →
    gs (𝟙 X) z (W ⊓ L.U k) (s k) =
      (gm (𝟙 X) z (L.U k ⊓ L.U k') (L.g k k') : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k') (s k')

def SecCarriedOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gs f z (W ⊓ L.U j) (s j) = (gw w (𝟙 X) z j k : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k) (s k)

example {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) (hT : IsFrameOver L W T) :
    IsSecOver L W (fun k => (T k).val) := by
  intro z k k' hz hk hk'
  have hm : z ∈ W ⊓ L.U k ⊓ (W ⊓ L.U k') := ⟨⟨hz, hk⟩, hz, hk'⟩
  have e := congrArg (fun u => (gm (𝟙 X) z _ u : X.presheaf.stalk z)) (hT k k')
  simp only [map_mul, Units.val_mul] at e
  rw [gm_res _ z _ hm, gm_res _ z _ hm, gm_res _ z _ hm] at e
  have h1 : (𝟙 X) z ∈ W ⊓ L.U k := ⟨hz, hk⟩
  have h2 : (𝟙 X) z ∈ W ⊓ L.U k' := ⟨hz, hk'⟩
  show gs (𝟙 X) z _ (T k).val = _ * gs (𝟙 X) z _ (T k').val
  rw [gs_unit _ z _ h1, gs_unit _ z _ h2]
  exact e

end GlobalTheory.Mum
