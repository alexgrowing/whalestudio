import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}}

def addCls (A : Over S) [GrpObj A] (T : Over S) : AddSubgroup (Pic (A ⊗ T).left) where
  carrier := {c | ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c}
  add_mem' {c d} hc hd Y a a' t := by
    simp only [map_add]
    rw [hc Y a a' t, hd Y a a' t]
    abel
  zero_mem' Y a a' t := by simp only [map_zero, add_zero]
  neg_mem' {c} hc Y a a' t := by
    simp only [map_neg]
    rw [hc Y a a' t]
    abel

variable {A : Over S} [GrpObj A]

theorem fam_iff_mem {T : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) : Fam A N ↔ cls N hN ∈ addCls A T :=
  ⟨fun h ↦ (isAdditive_iff hN).1 h.add, fun h ↦ ⟨hN, (isAdditive_iff hN).2 h⟩⟩

def resCls {T' T : Over S} (u : T' ⟶ T) : addCls A T →+ addCls A T' :=
  ((CechPic.pull (lift (fst A T') (snd A T' ≫ u)).left).comp (addCls A T).subtype).codRestrict _
    fun c Y a a' t ↦ by
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply, ← CechPic.pull_comp,
        ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
      exact c.2 Y a a' (t ≫ u)

variable (A) in

def famFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{1} where
  obj T := CommGrpCat.of (Multiplicative (addCls A T.unop))
  map g := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative (resCls (A := A) g.unop))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T.unop) (snd A T.unop ≫ 𝟙 _)).left _ = _
    rw [Category.comp_id, lift_fst_snd, Over.id_left, CechPic.pull_id]
    rfl
  map_comp {T T' T''} g g' := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop ≫ g.unop)).left _ =
      CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop)).left
        (CechPic.pull (lift (fst A T'.unop) (snd A T'.unop ≫ g.unop)).left _)
    rw [← CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]

section Rep

variable {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P)

include h

def ptCls (T : Over S) (x : T ⟶ B) : addCls A T :=
  ⟨evc h.fam.isLB (fst A T) (snd A T ≫ x), (fam_iff_mem (pull_isLB h.fam.isLB _)).1
    ⟨pull_isLB h.fam.isLB _, fun Y a a' t ↦ by
      refine (cls_eq_iff (pull_isLB (pull_isLB h.fam.isLB _) _)
        (isLB_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _))).1 ?_
      rw [cls_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _)]
      rw [cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _)]
      rw [evc_ev h.fam.isLB, evc_ev h.fam.isLB, evc_ev h.fam.isLB]
      simp only [lift_fst, lift_snd_assoc]
      exact (isAdditive_iff h.fam.isLB).1 h.fam.add Y _ _ _⟩⟩

theorem ptCls_bij (T : Over S) : Function.Bijective (ptCls h T) := by
  have hP := h.fam.isLB
  constructor
  · intro x x' e
    have hN : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hP _
    have fN : Fam A (ev P (fst A T) (snd A T ≫ x)) := (fam_iff_mem hN).2 (ptCls h T x).2
    refine (h.univ T (toUnit T) _ fN).unique ⟨toUnit_unique _ _, (cls_eq_iff hN hN).1 rfl⟩
      ⟨toUnit_unique _ _, (cls_eq_iff hN (pull_isLB hP _)).1 (congrArg Subtype.val e)⟩
  · intro c
    obtain ⟨N, hN, hc⟩ := cls_surj (c : Pic (A ⊗ T).left)
    have fN : Fam A N := (fam_iff_mem hN).2 (hc ▸ c.2)
    obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ T (toUnit T) N fN
    exact ⟨x, Subtype.ext (((cls_eq_iff hN (pull_isLB hP _)).2 hx).symm.trans hc)⟩

theorem ptCls_comp {T' T : Over S} (g : T' ⟶ T) (x : T ⟶ B) :
    ptCls h T' (g ≫ x) = resCls g (ptCls h T x) := by
  refine Subtype.ext ?_
  change evc h.fam.isLB (fst A T') (snd A T' ≫ g ≫ x) =
    CechPic.pull (lift (fst A T') (snd A T' ≫ g)).left (evc h.fam.isLB (fst A T) (snd A T ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

def famRep : (famFunctor A ⋙ forget CommGrpCat.{1}).RepresentableBy B where
  homEquiv {T} := (Equiv.ofBijective _ (ptCls_bij h T)).trans Multiplicative.ofAdd
  homEquiv_comp g x := ptCls_comp h g x

end Rep

end GlobalTheory.DualCon

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S} {P : LB (A ⊗ B).left}

theorem evc_eq_pull_ptCls (h : Rep A (toUnit B) P) {Y : Over S} (a : Y ⟶ A) (x : Y ⟶ B) :
    evc h.fam.isLB a x = CechPic.pull (lift a (𝟙 Y)).left (ptCls h Y x : Pic (A ⊗ Y).left) := by
  change _ = CechPic.pull (lift a (𝟙 Y)).left (evc h.fam.isLB (fst A Y) (snd A Y ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]

theorem rep_isDual : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left),
    Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  intro S A B _ P h
  have hP := h.fam.isLB
  letI inst : CommGrpObj B := CommGrpObj.ofRepresentableBy B _ (famRep h)
  have hmul : ∀ (Y : Over S) (x y : Y ⟶ B), ptCls h Y (x * y) = ptCls h Y x + ptCls h Y y := by
    have hμ : ptCls h (B ⊗ B) μ[B] = ptCls h _ (fst B B) + ptCls h _ (snd B B) :=
      Equiv.ofBijective_apply_symm_apply (ptCls h (B ⊗ B)) (ptCls_bij h _) _
    intro Y x y
    rw [Hom.mul_def, ptCls_comp, hμ, map_add, ← ptCls_comp, ← ptCls_comp, lift_fst, lift_snd]
  have hone : ∀ (Y : Over S), ptCls h Y (1 : Y ⟶ B) = 0 := by
    have hη : ptCls h (𝟙_ (Over S)) η[B] = 0 :=
      Equiv.ofBijective_apply_symm_apply (ptCls h _) (ptCls_bij h _) 0
    intro Y
    rw [Hom.one_def, ptCls_comp, hη, map_zero]
  refine ⟨inferInstance, inferInstance, ⟨hP, h.fam.add, ?_, fun T M hM hA ↦ ?_⟩, ?_⟩
  · rw [triv_ev_iff hP, evc_eq_pull_ptCls h, hone, ZeroMemClass.coe_zero, map_zero]
  · obtain ⟨x, ⟨-, hx⟩, hu⟩ := h.univ T (toUnit T) M ⟨hM, hA⟩
    exact ⟨x, hx, fun y hy ↦ hu y ⟨toUnit_unique _ _, hy⟩⟩
  · have hs : (swap P).IsLB := pull_isLB hP _
    refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
    rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_eq_pull_ptCls h, evc_eq_pull_ptCls h,
      evc_eq_pull_ptCls h, hmul, AddSubgroup.coe_add, map_add]

end GlobalTheory.DualCon
