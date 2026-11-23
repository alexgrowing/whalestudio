import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBFrameEx

variable {X : Scheme.{0}}

private theorem res_res' {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem coc {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens} (h₁ : W ≤ L.U i ⊓ L.U j)
    (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  have := congrArg (res hW) (hL.cocycle i j k)
  rwa [map_mul, res_res', res_res', res_res'] at this

structure Ch (L : LB X) where
  U : X.affineOpens
  m : L.ι
  le : (U : X.Opens) ≤ L.U m

instance (L : LB X) : Preorder (Ch L) where
  le a b := (b.U : X.Opens) ≤ a.U
  le_refl _ := le_rfl
  le_trans _ _ _ h h' := h'.trans h

abbrev opF (L : LB X) : Ch L ⥤ AffOp X where
  obj T := Opposite.op T.U
  map a := (homOfLE (leOfHom a)).op

def unit (L : LB X) (T T' : Ch L) (a : T ⟶ T') : Γ(X, opOf (opF L) T')ˣ :=
  res (le_inf T'.le ((show (T'.U : X.Opens) ≤ T.U from leOfHom a).trans T.le) : (T'.U : X.Opens) ≤ L.U T'.m ⊓ L.U T.m) (L.g T'.m T.m)

def gen (L : LB X) (T : Ch L) (m : L.ι) : Γ(X, opOf (opF L) T ⊓ L.U m)ˣ :=
  res (le_inf inf_le_right (inf_le_left.trans T.le) : (T.U : X.Opens) ⊓ L.U m ≤ L.U m ⊓ L.U T.m) (L.g m T.m)

theorem isBas (L : LB X) (hL : L.IsLB) : IsBas (opOf (opF L)) := by
  have hch : ∀ x : X, ∃ m, x ∈ L.U m := fun x => by
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← hL.cover] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  refine ⟨fun x U hx => ?_, fun t₁ t₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨m, hm⟩ := hch x
    obtain ⟨V, hV, hxV, hVU⟩ := hb (show x ∈ U ⊓ L.U m from ⟨hx, hm⟩)
    exact ⟨⟨⟨V, hV⟩, m, hVU.trans inf_le_right⟩, hxV, hVU.trans inf_le_left⟩
  · obtain ⟨V, hV, hxV, hVU⟩ := hb (show x ∈ U ⊓ (opOf (opF L) t₁ ⊓ opOf (opF L) t₂) from ⟨hx, h₁, h₂⟩)
    refine ⟨⟨⟨V, hV⟩, t₁.m, (hVU.trans inf_le_right).trans (inf_le_left.trans t₁.le)⟩,
      ⟨homOfLE ?_⟩, ⟨homOfLE ?_⟩, hxV, hVU.trans inf_le_left⟩
    · exact (hVU.trans inf_le_right).trans inf_le_left
    · exact (hVU.trans inf_le_right).trans inf_le_right

theorem isFrame (L : LB X) (hL : L.IsLB) : IsFrame L (opOf (opF L)) (opOf_le (opF L)) (unit L) := by
  refine ⟨gen L, fun T m m' => ?_, fun T T' a m => ?_⟩
  · simp only [gen]
    rw [res_res', res_res']
    exact (coc hL m m' T.m _ _ _).symm
  · simp only [gen, unit]
    rw [res_res', res_res']
    rw [mul_comm]
    exact (coc hL m T'.m T.m _ _ _).symm

theorem exists_frame : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C)
    (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ),
    IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u :=
  fun X L hL => ⟨Ch L, inferInstance, fun _ _ => inferInstance, opF L, unit L, isBas L hL, isFrame L hL⟩

end GlobalTheory.LBFrameEx
