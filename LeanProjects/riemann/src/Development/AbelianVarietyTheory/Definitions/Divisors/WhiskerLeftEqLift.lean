import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {X Y : Scheme.{0}}

structure IsOn (W : X.Opens) (L : LB X) : Prop where
  le : ∀ a, L.U a ≤ W
  cov : ∀ x ∈ W, ∃ a, x ∈ L.U a
  coc : ∀ (x : X) (a b c : L.ι), x ∈ L.U a → x ∈ L.U b → x ∈ L.U c →
    gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b c) = gm (𝟙 X) x _ (L.g a c)

abbrev Cmp (W : X.Opens) (L M : LB X) : Type := ∀ (a : L.ι) (b : M.ι), Γ(X, W ⊓ (L.U a ⊓ M.U b))ˣ

def IsoOn (W : X.Opens) (L M : LB X) (w : Cmp W L M) : Prop :=
  ∀ x ∈ W, ∀ (a a' : L.ι) (b b' : M.ι), x ∈ L.U a → x ∈ L.U a' → x ∈ M.U b → x ∈ M.U b' →
    gm (𝟙 X) x _ (w a b) * gm (𝟙 X) x _ (M.g b b') = gm (𝟙 X) x _ (L.g a a') * gm (𝟙 X) x _ (w a' b')

abbrev RigD (e : Y ⟶ X) (L : LB X) : Type := ∀ a : L.ι, Γ(Y, e ⁻¹ᵁ L.U a)ˣ

def RigOn (e : Y ⟶ X) (L : LB X) (r : RigD e L) : Prop :=
  ∀ (y : Y) (a b : L.ι), e y ∈ L.U a → e y ∈ L.U b →
    gm (𝟙 Y) y _ (r a) = gm e y _ (L.g a b) * gm (𝟙 Y) y _ (r b)

def Norm (e : Y ⟶ X) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : RigD e L) (r' : RigD e M) : Prop :=
  ∀ (y : Y) (a : L.ι) (b : M.ι), e y ∈ W → e y ∈ L.U a → e y ∈ M.U b →
    gm e y _ (w a b) * gm (𝟙 Y) y _ (r' b) = gm (𝟙 Y) y _ (r a)

def FnBij (p : X ⟶ Y) : Prop := ∀ V : Y.Opens, Function.Bijective (p.app V).hom

theorem isOn_top {L : LB X} (hL : L.IsLB) : IsOn ⊤ L :=
  ⟨fun _ ↦ le_top, fun x _ ↦ exists_chart hL x, fun x _ _ _ ha hb hc ↦ gm_cocycle hL (𝟙 X) x ha hb hc⟩

theorem fnBij_id : FnBij (𝟙 X) := fun _ ↦ Function.bijective_id

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def AddCls {T : Over S} (c : Pic (A ⊗ T).left) : Prop :=
  ∀ (Z : Over S) (a a' : Z ⟶ A) (t : Z ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c

theorem AddCls.pull {T T' : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) (u : T' ⟶ T) :
    AddCls A (CechPic.pull (A ◁ u).left c) := fun Z a a' t ↦ by
  simpa only [← pull_comp, ← Over.comp_left, lift_whiskerLeft] using h Z a a' (t ≫ u)

def addF : (Over S)ᵒᵖ ⥤ Type 1 where
  obj T := {c : Pic (A ⊗ T.unop).left // AddCls A c}
  map u := TypeCat.ofHom fun c ↦ ⟨CechPic.pull (A ◁ u.unop).left c.1, c.2.pull A u.unop⟩
  map_id T := by
    ext c
    change CechPic.pull (A ◁ 𝟙 T.unop).left c.1 = c.1
    rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]
  map_comp u v := by
    ext c
    change CechPic.pull (A ◁ (v.unop ≫ u.unop)).left c.1 =
      CechPic.pull (A ◁ v.unop).left (CechPic.pull (A ◁ u.unop).left c.1)
    rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem addF_map_val {T T' : Over S} (u : T' ⟶ T) (c : (addF A).obj (Opposite.op T)) :
    ((addF A).map u.op c).1 = CechPic.pull (A ◁ u).left c.1 := rfl

variable {A}

def famCls {T : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) : (addF A).obj (Opposite.op T) :=
  ⟨cls N h.isLB, (isAdditive_iff h.isLB).1 h.add⟩

theorem famCls_surj {T : Over S} (c : (addF A).obj (Opposite.op T)) :
    ∃ (N : LB (A ⊗ T).left) (h : Fam A N), famCls h = c := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact ⟨N, ⟨hN, (isAdditive_iff hN).2 hc⟩, rfl⟩

omit [GrpObj A] in

theorem whiskerLeft_eq_lift {T T' : Over S} (u : T' ⟶ T) : A ◁ u = lift (fst A T') (snd A T' ≫ u) := by
  ext <;> simp

theorem same_iff_map {T U Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M)
    (y : Z ⟶ T) (u : Z ⟶ U) : Same A N M y u ↔ (addF A).map y.op (famCls hN) = (addF A).map u.op (famCls hM) := by
  refine (same_iff hN.isLB hM.isLB y u).trans (Iff.trans ?_ Subtype.ext_iff.symm)
  rw [addF_map_val, addF_map_val, whiskerLeft_eq_lift, whiskerLeft_eq_lift]
  rfl

end GlobalTheory.PicGlue
