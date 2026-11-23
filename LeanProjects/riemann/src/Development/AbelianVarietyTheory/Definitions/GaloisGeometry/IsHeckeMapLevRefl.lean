import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFullSetCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetIsHeckeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtModelForgetFiniteEtale

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory GlobalTheory.AV GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

namespace LevRep

variable {N : ℕ} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}

def univAct (M : LevRep b N w m e) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : ObjLev b N w m e M.s :=
  ⟨M.univ.obj, GlobalTheory.LevDict.htLevelAct M.univ.lev g⟩

def levAct (M : LevRep b N w m e) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.X ⟶ M.X :=
  (M.rep M.X M.s (M.univAct g)).exists.choose

variable (M : LevRep b N w m e)

theorem levAct_spec (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) :
    M.levAct g ≫ M.s = M.s ∧ ObjLevMap (M.univAct g) M.univ (M.levAct g) :=
  (M.rep M.X M.s (M.univAct g)).exists.choose_spec

@[simp] theorem levAct_comp_s (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.levAct g ≫ M.s = M.s := (M.levAct_spec g).1

theorem eq_levAct (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) (f : M.X ⟶ M.X) (h₁ : f ≫ M.s = M.s)
    (h₂ : ObjLevMap (M.univAct g) M.univ f) : f = M.levAct g :=
  (M.rep M.X M.s (M.univAct g)).unique ⟨h₁, h₂⟩ (M.levAct_spec g)

@[simp] theorem levAct_one : M.levAct 1 = 𝟙 M.X := by
  refine (M.eq_levAct 1 (𝟙 _) (Category.id_comp _) ⟨GlobalTheory.UPel.HT.EtLev.LevForget.idMap M.univ.obj, fun x => ?_⟩).symm
  show (M.univ.lev.α ((1 : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)).val.mulVec x)).left ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

theorem levAct_mul (h g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) :
    M.levAct (h * g) = M.levAct h ≫ M.levAct g := by
  symm
  obtain ⟨φh, hh⟩ := (M.levAct_spec h).2
  obtain ⟨φg, hg⟩ := (M.levAct_spec g).2
  have hh' : ∀ y, (M.univ.lev.α (h.val.mulVec y)).left ≫ φh.φ = M.levAct h ≫ (M.univ.lev.α y).left := hh
  have hg' : ∀ y, (M.univ.lev.α (g.val.mulVec y)).left ≫ φg.φ = M.levAct g ≫ (M.univ.lev.α y).left := hg
  refine M.eq_levAct (h * g) _ (by rw [Category.assoc, levAct_comp_s, levAct_comp_s]) ⟨ObjMap.comp φh φg, fun x => ?_⟩
  have e1 : (h * g).val.mulVec x = h.val.mulVec (g.val.mulVec x) := by rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  show (M.univ.lev.α ((h * g).val.mulVec x)).left ≫ (φh.φ ≫ φg.φ) = (M.levAct h ≫ M.levAct g) ≫ _
  rw [e1]
  erw [← Category.assoc, hh', Category.assoc, hg']
  simp only [Category.assoc]

@[simp] theorem levAct_inv_comp (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.levAct g⁻¹ ≫ M.levAct g = 𝟙 M.X := by
  rw [← levAct_mul, inv_mul_cancel, levAct_one]

@[simp] theorem levAct_comp_inv (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.levAct g ≫ M.levAct g⁻¹ = 𝟙 M.X := by
  rw [← levAct_mul, mul_inv_cancel, levAct_one]

def levActIso (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.X ≅ M.X :=
  ⟨M.levAct g, M.levAct g⁻¹, M.levAct_comp_inv g, M.levAct_inv_comp g⟩

def levActOp : (GL (Fin D.n) (𝓞 D.F ⧸ w ^ m))ᵐᵒᵖ →* End M.X where
  toFun g := M.levAct g.unop
  map_one' := M.levAct_one
  map_mul' a b := by
    rw [MulOpposite.unop_mul, levAct_mul]
    rfl

def levActHom : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m) →* End M.X where
  toFun g := M.levAct g⁻¹
  map_one' := by rw [inv_one]; exact M.levAct_one
  map_mul' a b := by
    rw [mul_inv_rev, levAct_mul]
    rfl

@[simp] theorem levAct_forget (F₀ : RepFam b N) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) :
    M.levAct g ≫ M.forget F₀ = M.forget F₀ := by
  have hf := (F₀.rep M.X M.s M.univ.obj).exists.choose_spec
  obtain ⟨φg, -⟩ := (M.levAct_spec g).2
  exact (F₀.rep M.X M.s M.univ.obj).unique
    ⟨by rw [Category.assoc]; erw [hf.1]; exact M.levAct_comp_s g, ⟨ObjMap.comp φg hf.2.some⟩⟩ hf

end LevRep

section Hecke

variable {G : HTGroup p} (L : Link D G)

abbrev TIsoAt {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : Obj b N s) {k : Type} [Field k] (t : Sp k ⟶ S) : Type :=
  TateIsoO D k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def InducesAt {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : Obj b N s) {k : Type} [Field k] (t : Sp k ⟶ S)
    (I : TIsoAt o t) : Prop :=
  ∀ y, toUnit _ ≫ o.eta y = I.ev N y

def ActsAt {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} {o' : Obj b N' s} {o'' : Obj b N s} {k : Type} [Field k]
    {t : Sp k ⟶ S} (I' : TIsoAt o' t) (I'' : TIsoAt o'' t) (ψ : o'.A ⟶ o''.A) (m : ℤ) (g : G.GAf) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
    I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, m • L.actG g (inAf D x) = inAf D y + n • v

def IsIsogWit (g : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} (o' : Obj b N' s) (o'' : Obj b N s)
    (ψ : o'.A ⟶ o''.A) (ψ' : o''.A ⟶ o'.A) (m d : ℕ) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
    ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ m.Coprime p ∧ d.Coprime p ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : R →+* k), t ≫ s = spMap β →
      ∃ (I' : TIsoAt o' t) (I'' : TIsoAt o'' t), InducesAt o' t I' ∧ InducesAt o'' t I'' ∧
        ActsAt L I' I'' ψ m g

def IsHeckeWit (g : G.GAf) {N N' : ℕ} (M' : Model b N') (M : Model b N) (q : M'.X ⟶ M.X) (o'' : Obj b N M'.s)
    (ψ : M'.univ.A ⟶ o''.A) (ψ' : o''.A ⟶ M'.univ.A) (m d : ℕ) (φ : ObjMap o'' M.univ q) : Prop :=
  q ≫ M.s = M'.s ∧ IsIsogWit L g M'.univ o'' ψ ψ' m d

def IsHeckeMapLev (g : G.GAf) {N N' : ℕ} {M' : Model b N'} {M : Model b N} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}
    (Mm' : LevRep b N' w m e) (Mm : LevRep b N w m e) (q : M'.X ⟶ M.X) (o'' : Obj b N M'.s)
    (ψ : M'.univ.A ⟶ o''.A) (ψ' : o''.A ⟶ M'.univ.A) (c d : ℕ) (φ : ObjMap o'' M.univ q)
    (φ' : ObjMap Mm'.univ.obj M'.univ (Mm'.forget M'.toRepFam)) (φ₀ : ObjMap Mm.univ.obj M.univ (Mm.forget M.toRepFam))
    (qm : Mm'.X ⟶ Mm.X) : Prop :=
  IsHeckeWit L g M' M q o'' ψ ψ' c d φ ∧ qm ≫ Mm.forget M.toRepFam = Mm'.forget M'.toRepFam ≫ q ∧
    ∀ x, qm ≫ (Mm.univ.lev.α (c • x)).left ≫ φ₀.φ = (Mm'.univ.lev.α x).left ≫ φ'.φ ≫ ψ.left ≫ φ.φ

end Hecke

section Basic₂

variable {N : ℕ} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}

example (M : LevRep b N w m e) : M.levActHom 1 = 𝟙 M.X := M.levActHom.map_one

example (M : LevRep b N w m e) (x : Fin D.n → 𝓞 D.F ⧸ w ^ m) : (M.univAct 1).lev.α x = M.univ.lev.α x := by
  simp [LevRep.univAct]

example (M : LevRep b N w m e) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : IsIso (M.levAct g) :=
  (M.levActIso g).isIso_hom

end Basic₂

end GlobalTheory.DrinLev.HT
