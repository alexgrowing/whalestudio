import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}} {O : Type} [Ring O]

def IsRAct (A : Over S) [GrpObj A] (act : O → (A ⟶ A)) : Prop :=
  (∀ a, IsMonHom (act a)) ∧ act 1 = 𝟙 A ∧ (∀ a b, act (a * b) = act a ≫ act b) ∧
    ∀ a b, act (a + b) = act a * act b

def Adj (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) (bar : O → O) (act : O → (A ⟶ A)) : Prop :=
  ∀ a, LBIso (Q.pull (lift (fst A A ≫ act a) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar a))).left)

structure ActRep (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) (bar : O → O) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grp : GrpObj AH]
  φ : AH.left ⟶ A.left
  φ₂ : (AH ⊗ AH).left ⟶ (A ⊗ A).left
  pb : IsGrpPullback AH A π φ
  sq : IsSquare φ φ₂
  act : O → (AH ⟶ AH)
  isAct : IsRAct AH act
  adj : Adj AH (Q.pull φ₂) bar act
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left)
    (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (act' : O → (A' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' →
    IsRAct A' act' → Adj A' (Q.pull φ₂') bar act' →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ ψ : A'.left ⟶ AH.left, IsGrpPullback A' AH h ψ ∧ ψ ≫ φ = φ' ∧
      ∀ a, (act' a).left ≫ ψ = ψ ≫ (act a).left

attribute [instance] ActRep.grp

theorem IsRAct.of_oAct {O : Type} [CommRing O] {A : Over S} [GrpObj A] (i : OAct O A) : IsRAct A i.act :=
  ⟨i.hom, i.one, i.mul, i.add⟩

theorem IsRAct.op_of_ringAct {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A O) :
    IsRAct A (fun a : Oᵐᵒᵖ => ρ.act a.unop) :=
  ⟨fun _ => ρ.hom _, ρ.map_one, fun _ _ => ρ.map_mul _ _, fun _ _ => ρ.map_add _ _⟩

def IsRAct.toRingAct {A : Over S} [GrpObj A] [IsCommMonObj A] {act : Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act) :
    Out.RingAct A O :=
  ⟨fun a => act (MulOpposite.op a), fun _ => h.1 _, h.2.1,
    fun a b => h.2.2.1 (MulOpposite.op b) (MulOpposite.op a), fun _ _ => h.2.2.2 _ _⟩

@[simp] theorem IsRAct.toRingAct_act {A : Over S} [GrpObj A] [IsCommMonObj A] {act : Oᵐᵒᵖ → (A ⟶ A)}
    (h : IsRAct A act) (a : O) : h.toRingAct.act a = act (MulOpposite.op a) := rfl

theorem IsRAct.toRingAct_op_of_ringAct {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A O) (a : O) :
    (IsRAct.op_of_ringAct ρ).toRingAct.act a = ρ.act a := rfl

def IsRAct.toOAct {O : Type} [CommRing O] {A : Over S} [GrpObj A] {act : O → (A ⟶ A)} (h : IsRAct A act) :
    OAct O A :=
  ⟨act, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

@[simp] theorem IsRAct.toOAct_act {O : Type} [CommRing O] {A : Over S} [GrpObj A] {act : O → (A ⟶ A)}
    (h : IsRAct A act) : h.toOAct.act = act := rfl

theorem IsRAct.act_mul_comm {O : Type} [CommRing O] {A : Over S} [GrpObj A] {act : O → (A ⟶ A)}
    (h : IsRAct A act) (a b : O) : act (a * b) = act b ≫ act a := by
  rw [mul_comm]; exact h.2.2.1 b a

theorem IsRAct.comp_comm {O : Type} [CommRing O] {A : Over S} [GrpObj A] {act : O → (A ⟶ A)}
    (h : IsRAct A act) (a b : O) : act a ≫ act b = act b ≫ act a := by
  rw [← h.2.2.1, ← h.2.2.1, mul_comm]

example (A : Over S) [GrpObj A] (act : O → (A ⟶ A)) (h : IsRAct A act) (a : O) : act (a * 1) = act a := by
  rw [h.2.2.1, h.2.1, Category.comp_id]

example {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A O) (a b : O) :
    ρ.act (b * a) = ρ.act a ≫ ρ.act b :=
  (IsRAct.op_of_ringAct ρ).2.2.1 (MulOpposite.op a) (MulOpposite.op b)

example {O : Type} [CommRing O] {A : Over S} [GrpObj A] (i : OAct O A) : (IsRAct.of_oAct i).toOAct = i := rfl

end GlobalTheory.EndLoc
