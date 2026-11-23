import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DieuUnifDiagNotSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LubinTateDeformation

noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.VDefo

open GlobalTheory.VDiv GlobalTheory.PDiv

section LocAlg

variable (O Or : Type) [CommRing O] [CommRing Or] [IsLocalRing Or] [Algebra O Or]

structure LocAlg : Type 1 where

  A : Type
  [ring : CommRing A]
  [isLocalRing : IsLocalRing A]
  [algOr : Algebra Or A]
  [algO : Algebra O A]
  [tower : IsScalarTower O Or A]
  [isLocalHom : IsLocalHom (algebraMap Or A)]

  bij : Function.Bijective (ResidueField.map (algebraMap Or A))

attribute [instance] LocAlg.ring LocAlg.isLocalRing LocAlg.algOr LocAlg.algO LocAlg.tower
  LocAlg.isLocalHom

namespace LocAlg

variable {O Or}

def red (A : LocAlg O Or) : A.A →+* ResidueField Or := FOM.resRed Or A.A A.bij

theorem red_eq_zero (A : LocAlg O Or) {a : A.A} (ha : a ∈ maximalIdeal A.A) : A.red a = 0 := by
  simp [red, FOM.resRed, (residue_eq_zero_iff a).2 ha]

@[ext] structure Hom (A B : LocAlg O Or) : Type where

  f : A.A →ₐ[Or] B.A

  isLocal : IsLocalHom (f : A.A →+* B.A)

instance : Category (LocAlg O Or) where
  Hom := Hom
  id A := ⟨AlgHom.id Or A.A, ⟨fun _ h => h⟩⟩
  comp f g := ⟨g.f.comp f.f, ⟨fun a h => f.isLocal.map_nonunit a (g.isLocal.map_nonunit (f.f a) h)⟩⟩
  id_comp f := Hom.ext (AlgHom.comp_id _)
  comp_id f := Hom.ext (AlgHom.id_comp _)
  assoc f g h := Hom.ext (AlgHom.comp_assoc _ _ _).symm

@[simp] theorem comp_f {A B C : LocAlg O Or} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.f (f ≫ g) = g.f.comp f.f := rfl

@[simp] theorem id_f (A : LocAlg O Or) : Hom.f (𝟙 A) = AlgHom.id Or A.A := rfl

@[simp] theorem red_algebraMap (A : LocAlg O Or) (r : Or) : A.red (algebraMap Or A.A r) = residue Or r := by
  simp only [red, FOM.resRed, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.symm_apply_eq]
  simp [ResidueField.map_residue]

theorem red_comp {A B : LocAlg O Or} (f : A ⟶ B) (a : A.A) : B.red (f.f a) = A.red a := by
  obtain ⟨r, hr⟩ := (A.bij.2 (residue A.A a))
  obtain ⟨r, rfl⟩ := residue_surjective r
  have h1 : a - algebraMap Or A.A r ∈ maximalIdeal A.A := by
    rw [← residue_eq_zero_iff, map_sub, ← hr, ResidueField.map_residue, sub_self]
  have h2 : f.f a - algebraMap Or B.A r ∈ maximalIdeal B.A := by
    rw [← AlgHom.commutes f.f r, ← map_sub]
    haveI := f.isLocal
    exact map_nonunit (f.f : A.A →+* B.A) _ h1
  have e : ∀ (C : LocAlg O Or) (x : C.A), x - algebraMap Or C.A r ∈ maximalIdeal C.A →
      C.red x = residue Or r := fun C x hx => by
    have := C.red_eq_zero hx
    rw [map_sub, sub_eq_zero] at this
    rw [this]
    simp only [red, FOM.resRed, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq]
    simp [ResidueField.map_residue]
  rw [e B _ h2, e A _ h1]

def residueField : LocAlg O Or where
  A := ResidueField Or
  isLocalHom := ⟨fun a h => by
    by_contra ha
    exact h.ne_zero ((residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 ha))⟩
  bij := ⟨RingHom.injective _, fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := residue_surjective x
    refine ⟨residue Or r, ?_⟩
    rw [ResidueField.map_residue]
    rfl⟩

abbrev Trunc (R : LocAlg O Or) (k : ℕ) : Type := R.A ⧸ maximalIdeal R.A ^ (k + 1)

def truncRed (R : LocAlg O Or) (k : ℕ) : R.Trunc k →+* ResidueField Or :=
  Ideal.Quotient.lift _ R.red fun _ ha => R.red_eq_zero (Ideal.pow_le_self (Nat.succ_ne_zero k) ha)

def truncMap (R : LocAlg O Or) (k : ℕ) : R.Trunc (k + 1) →+* R.Trunc k :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))

def truncLift {R A : LocAlg O Or} (g : R ⟶ A) (k : ℕ) (hk : ∀ x ∈ maximalIdeal R.A ^ (k + 1), g.f x = 0) :
    R.Trunc k →+* A.A :=
  Ideal.Quotient.lift _ (g.f : R.A →+* A.A) hk

abbrev mapMax (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] : Ideal M :=
  Ideal.map (algebraMap R.A M) (maximalIdeal R.A)

def truncTensor (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) :
    R.Trunc (k + 1) ⊗[R.A] M →ₐ[R.A] R.Trunc k ⊗[R.A] M :=
  Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R.A (Ideal.pow_le_pow_right (by omega)))
    (AlgHom.id R.A M)

@[simp] theorem truncTensor_tmul (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ)
    (r : R.A) (x : M) :
    R.truncTensor M k (Ideal.Quotient.mk _ r ⊗ₜ[R.A] x) = Ideal.Quotient.mk _ r ⊗ₜ[R.A] x := rfl

@[simp] theorem truncTensor_one_tmul (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ)
    (x : M) : R.truncTensor M k ((1 : R.Trunc (k + 1)) ⊗ₜ[R.A] x) = (1 : R.Trunc k) ⊗ₜ[R.A] x :=
  R.truncTensor_tmul M k 1 x

def truncQuot (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) :
    M ⧸ R.mapMax M ^ (k + 1) ≃+* R.Trunc k ⊗[R.A] M :=
  (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _).symm).trans
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor M (maximalIdeal R.A ^ (k + 1))).toRingEquiv

@[simp] theorem truncQuot_mk (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) (x : M) :
    R.truncQuot M k (Ideal.Quotient.mk _ x) = (1 : R.Trunc k) ⊗ₜ[R.A] x := by
  simp [truncQuot]

theorem truncQuot_symm_tmul (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) (x : M) :
    (R.truncQuot M k).symm ((1 : R.Trunc k) ⊗ₜ[R.A] x) = Ideal.Quotient.mk _ x := by
  rw [RingEquiv.symm_apply_eq, truncQuot_mk]

theorem truncQuot_symm_truncTensor (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ)
    (z : R.Trunc (k + 1) ⊗[R.A] M) :
    (R.truncQuot M k).symm (R.truncTensor M k z) =
      Ideal.Quotient.factorPow (R.mapMax M) (Nat.le_succ (k + 1)) ((R.truncQuot M (k + 1)).symm z) := by
  obtain ⟨w, rfl⟩ := (R.truncQuot M (k + 1)).surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [RingEquiv.symm_apply_apply, truncQuot_mk, truncTensor_one_tmul, truncQuot_symm_tmul]
  rfl

end LocAlg

end LocAlg

section Cart

variable {p : ℕ}

def IsCart {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {G' : PDivGroup p R'}
    {G : PDivGroup p R} (s : PDivGroup.SemiHom σ G' G) : Prop :=
  letI := σ.toAlgebra; IsIso (PDivGroup.SemiHom.lift s)

end Cart

section Defo

variable (p : ℕ) [Fact p.Prime] {O Or : Type} [CommRing O] [CommRing Or] [IsLocalRing Or]
  [Algebra O Or] (Hb : VarpiDivModule p O (ResidueField Or))

structure Defo (S : Type) [CommRing S] [Algebra O S] (red : S →+* ResidueField Or) : Type 1 where

  H : VarpiDivModule p O S

  s : PDivGroup.SemiHom red Hb.G H.G

  cart : IsCart s

  comm : ∀ (c : O) (n : ℕ) (a : H.G.A n),
    s.app n (PDivGroup.Hom.app (H.ι c) n a) = PDivGroup.Hom.app (Hb.ι c) n (s.app n a)

variable {p Hb}

section Iso

variable {S : Type} [CommRing S] [Algebra O S] {red : S →+* ResidueField Or}

structure DefoIso (D D' : Defo p Hb S red) : Type where

  e : D.H ≅ D'.H

  compat : ∀ n a, D.s.app n (PDivGroup.Hom.app e.hom.f n a) = D'.s.app n a

def DefoIso.refl (D : Defo p Hb S red) : DefoIso D D := ⟨Iso.refl _, fun _ _ => rfl⟩

def DefoIso.symm {D D' : Defo p Hb S red} (i : DefoIso D D') : DefoIso D' D :=
  ⟨i.e.symm, fun n a => by
    have h := congrArg (fun g : D.H ⟶ D.H => PDivGroup.Hom.app g.f n a) i.e.hom_inv_id
    simp only [VarpiDivModule.comp_f, VarpiDivModule.id_f, PDivGroup.comp_app,
      PDivGroup.id_app] at h
    rw [← i.compat n]
    exact congrArg (D.s.app n) h⟩

def DefoIso.trans {D D' D'' : Defo p Hb S red} (i : DefoIso D D') (j : DefoIso D' D'') :
    DefoIso D D'' :=
  ⟨i.e.trans j.e, fun n a => by
    simp only [Iso.trans_hom, VarpiDivModule.comp_f, PDivGroup.comp_app]
    exact (i.compat n _).trans (j.compat n a)⟩

variable (p Hb S red) in

def defoSetoid : Setoid (Defo p Hb S red) where
  r D D' := Nonempty (DefoIso D D')
  iseqv := ⟨fun D => ⟨DefoIso.refl D⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

end Iso

variable (p Hb) in

def DefFun (A : LocAlg O Or) : Type 1 := Quotient (defoSetoid p Hb A.A A.red)

def IsPush {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} (f : S →+* S')
    (D : Defo p Hb S red) (D' : Defo p Hb S' red') : Prop :=
  ∃ t : PDivGroup.SemiHom f D'.H.G D.H.G, IsCart t ∧
    (∀ (c : O) (n : ℕ) (a : D.H.G.A n),
      t.app n (PDivGroup.Hom.app (D.H.ι c) n a) = PDivGroup.Hom.app (D'.H.ι c) n (t.app n a)) ∧
    ∀ n a, D'.s.app n (t.app n a) = D.s.app n a

structure Push {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} (f : S →+* S')
    (D : Defo p Hb S red) (D' : Defo p Hb S' red') : Type where

  t : PDivGroup.SemiHom f D'.H.G D.H.G

  cart : IsCart t

  comm : ∀ (c : O) (n : ℕ) (a : D.H.G.A n),
    t.app n (PDivGroup.Hom.app (D.H.ι c) n a) = PDivGroup.Hom.app (D'.H.ι c) n (t.app n a)

  s_app : ∀ n a, D'.s.app n (t.app n a) = D.s.app n a

theorem Push.isPush {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} {f : S →+* S'}
    {D : Defo p Hb S red} {D' : Defo p Hb S' red'} (P : Push f D D') : IsPush f D D' :=
  ⟨P.t, P.cart, P.comm, P.s_app⟩

theorem isPush_iff_nonempty {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} {f : S →+* S'}
    {D : Defo p Hb S red} {D' : Defo p Hb S' red'} : IsPush f D D' ↔ Nonempty (Push f D D') :=
  ⟨fun ⟨t, h1, h2, h3⟩ => ⟨⟨t, h1, h2, h3⟩⟩, fun ⟨P⟩ => P.isPush⟩

variable (p Hb) in

structure ProRep (R : LocAlg O Or) : Type 1 where
  [noeth : IsNoetherianRing R.A]
  [complete : IsAdicComplete (maximalIdeal R.A) R.A]

  univ : ∀ k : ℕ, Defo p Hb (R.Trunc k) (R.truncRed k)

  tr : ∀ k, Push (R.truncMap k) (univ (k + 1)) (univ k)

  universal : ∀ (A : LocAlg O Or) [IsArtinianRing A.A] (D : Defo p Hb A.A A.red),
    ∃! g : R ⟶ A, ∃ (k : ℕ) (hk : ∀ x ∈ maximalIdeal R.A ^ (k + 1), g.f x = 0),
      IsPush (LocAlg.truncLift g k hk) (univ k) D

theorem ProRep.trans {R : LocAlg O Or} (U : ProRep p Hb R) (k : ℕ) :
    IsPush (R.truncMap k) (U.univ (k + 1)) (U.univ k) :=
  (U.tr k).isPush

end Defo

section Level

def evBC {S B : Type} [CommRing S] [CommRing B] [Algebra S B] (R' : Type) [CommRing R']
    [Algebra S R'] (x : B →ₐ[S] R') : R' ⊗[S] B →ₐ[R'] R' :=
  Algebra.TensorProduct.lift (AlgHom.id R' R') x fun _ _ => Commute.all _ _

def IsFullSet {S B T J : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing T] [Algebra S T]
    (P : J → (B →ₐ[S] T)) : Prop :=
  Finite J ∧ ∀ (R' : Type) [CommRing R'] [Nontrivial R'] [Algebra S R'] (j : T →ₐ[S] R'),
    Module.Free R' (R' ⊗[S] B) ∧ Module.Finite R' (R' ⊗[S] B) ∧
      Module.finrank R' (R' ⊗[S] B) = Nat.card J ∧
      ∀ f : R' ⊗[S] B, Algebra.norm R' f = ∏ᶠ i, evBC R' (j.comp (P i)) f

theorem IsFullSet.comp_equiv {S B T J J' : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing T]
    [Algebra S T] {P : J → (B →ₐ[S] T)} (h : IsFullSet P) (e : J' ≃ J) : IsFullSet (P ∘ e) := by
  refine ⟨(Equiv.finite_iff e).2 h.1, fun R' _ _ _ j => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.2 R' j
  refine ⟨h1, h2, h3.trans (Nat.card_congr e).symm, fun f => (h4 f).trans ?_⟩
  exact (finprod_comp_equiv e (f := fun i => evBC R' (j.comp (P i)) f)).symm

theorem IsFullSet.comp {S B T T' J : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing T]
    [Algebra S T] [CommRing T'] [Algebra S T'] {P : J → (B →ₐ[S] T)} (h : IsFullSet P)
    (g : T →ₐ[S] T') : IsFullSet fun i => g.comp (P i) :=
  ⟨h.1, fun R' _ _ _ j => by simpa only [AlgHom.comp_assoc] using h.2 R' (j.comp g)⟩

variable {p : ℕ} [Fact p.Prime] {O S : Type} [CommRing O] [CommRing S]

def torIdeal (G : PDivGroup p S) (ι : PDivGroup.Action O G) (ϖ : O) (m : ℕ) : Ideal (G.A m) :=
  kerIdeal (PDivGroup.Hom.app (ι (ϖ ^ m)) m)

variable [Algebra O S] (p)

@[ext] structure Level (G : PDivGroup p S) (ι : PDivGroup.Action O G) (ϖ : O) (n m : ℕ) (T : Type)
    [CommRing T] [Algebra S T] : Type where

  α : (Fin n → O ⧸ Ideal.span {ϖ ^ m}) → (G.A m →ₐ[S] T)

  tors : ∀ x, ∀ a ∈ torIdeal G ι ϖ m, α x a = 0

  map_add : ∀ x y, WithConv.toConv (α (x + y)) = WithConv.toConv (α x) * WithConv.toConv (α y)

  map_smul : ∀ (c : O) x,
    α (c • x) = (α x).comp (PDivGroup.Hom.app (ι c) m : G.A m →ₐ[S] G.A m)

  full : IsFullSet fun x => Ideal.Quotient.liftₐ (torIdeal G ι ϖ m) (α x) (tors x)

variable {p}

namespace Level

variable {G : PDivGroup p S} {ι : PDivGroup.Action O G} {ϖ : O} {n m : ℕ} {T T' : Type}
  [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T']

def map (L : Level p G ι ϖ n m T) (g : T →ₐ[S] T') : Level p G ι ϖ n m T' where
  α x := g.comp (L.α x)
  tors x a ha := by rw [AlgHom.comp_apply, L.tors x a ha, map_zero]
  map_add x y := by
    have h := congrArg (ptsPush (G.A m) g) (L.map_add x y)
    rw [map_mul] at h
    exact h
  map_smul c x := by rw [L.map_smul, AlgHom.comp_assoc]
  full := by
    have e : (fun x => Ideal.Quotient.liftₐ (torIdeal G ι ϖ m) (g.comp (L.α x))
        (fun a ha => by rw [AlgHom.comp_apply, L.tors x a ha, map_zero])) =
        fun x => g.comp (Ideal.Quotient.liftₐ (torIdeal G ι ϖ m) (L.α x) (L.tors x)) :=
      funext fun x => Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => rfl)
    rw [e]
    exact L.full.comp g

@[simp] theorem map_α (L : Level p G ι ϖ n m T) (g : T →ₐ[S] T') (x) : (L.map g).α x = g.comp (L.α x) :=
  rfl

def act (L : Level p G ι ϖ n m T) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) : Level p G ι ϖ n m T where
  α x := L.α (g.val.mulVec x)
  tors x := L.tors _
  map_add x y := by rw [Matrix.mulVec_add]; exact L.map_add _ _
  map_smul c x := by rw [Matrix.mulVec_smul]; exact L.map_smul _ _
  full := L.full.comp_equiv (glEquiv g).toEquiv

@[simp] theorem act_α (L : Level p G ι ϖ n m T) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (x) :
    (L.act g).α x = L.α (g.val.mulVec x) := rfl

theorem map_map {T'' : Type} [CommRing T''] [Algebra S T''] (L : Level p G ι ϖ n m T) (g : T →ₐ[S] T')
    (h : T' →ₐ[S] T'') : (L.map g).map h = L.map (h.comp g) :=
  Level.ext (funext fun _ => rfl)

@[simp] theorem map_id (L : Level p G ι ϖ n m T) : L.map (AlgHom.id S T) = L :=
  Level.ext (funext fun _ => AlgHom.id_comp _)

theorem act_map (L : Level p G ι ϖ n m T) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (h : T →ₐ[S] T') :
    (L.act g).map h = (L.map h).act g :=
  Level.ext (funext fun _ => rfl)

theorem act_mul (L : Level p G ι ϖ n m T) (a b : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    (L.act a).act b = L.act (a * b) :=
  Level.ext (funext fun x => by simp only [act_α, Units.val_mul, Matrix.mulVec_mulVec])

@[simp] theorem act_one (L : Level p G ι ϖ n m T) : L.act 1 = L :=
  Level.ext (funext fun x => by simp only [act_α, Units.val_one, Matrix.one_mulVec])

instance : MulAction (GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}))ᵐᵒᵖ (Level p G ι ϖ n m T) where
  smul g L := L.act g.unop
  one_smul L := Level.ext (funext fun x => by
    change L.α ((1 : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})).val.mulVec x) = L.α x
    rw [Units.val_one, Matrix.one_mulVec])
  mul_smul g h L := Level.ext (funext fun x => by
    change L.α ((h.unop * g.unop).val.mulVec x) = L.α (h.unop.val.mulVec (g.unop.val.mulVec x))
    rw [Units.val_mul, Matrix.mulVec_mulVec])

end Level

end Level

section LevelRep

variable {p : ℕ} [Fact p.Prime] {O Or : Type} [CommRing O] [CommRing Or] [IsLocalRing Or]
  [Algebra O Or] {Hb : VarpiDivModule p O (ResidueField Or)}

structure LevelRep {R : LocAlg O Or} (U : ProRep p Hb R) (ϖ : O) (n m : ℕ) : Type 1 where

  Rm : Type
  [ring : CommRing Rm]
  [alg : Algebra R.A Rm]

  [complete : IsAdicComplete (R.mapMax Rm) Rm]

  lev : ∀ k : ℕ, Level p (U.univ k).H.G (U.univ k).H.ι ϖ n m (R.Trunc k ⊗[R.A] Rm)

  compat : ∀ (k : ℕ) (x : Fin n → O ⧸ Ideal.span {ϖ ^ m}) (a : (U.univ (k + 1)).H.G.A m),
    (lev k).α x ((U.tr k).t.app m a) = R.truncTensor Rm k ((lev (k + 1)).α x a)

  rep : ∀ (k : ℕ) (B : Type) [CommRing B] [Algebra (R.Trunc k) B],
    Function.Bijective fun h : R.Trunc k ⊗[R.A] Rm →ₐ[R.Trunc k] B => (lev k).map h

attribute [instance] LevelRep.ring LevelRep.alg LevelRep.complete

variable {R : LocAlg O Or} {U : ProRep p Hb R} {ϖ : O} {n m : ℕ}

def LevelRep.aut (L : LevelRep U ϖ n m) (k : ℕ) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    R.Trunc k ⊗[R.A] L.Rm →ₐ[R.Trunc k] R.Trunc k ⊗[R.A] L.Rm :=
  (Equiv.ofBijective _ (L.rep k _)).symm ((L.lev k).act g)

namespace LevelRep

variable (L : LevelRep U ϖ n m)

theorem aut_spec (k : ℕ) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    (L.lev k).map (L.aut k g) = (L.lev k).act g :=
  Equiv.ofBijective_apply_symm_apply _ (L.rep k _) _

theorem aut_one (k : ℕ) : L.aut k 1 = AlgHom.id _ _ := by
  apply (L.rep k _).1
  change (L.lev k).map (L.aut k 1) = (L.lev k).map (AlgHom.id _ _)
  rw [L.aut_spec, Level.act_one, Level.map_id]

theorem aut_mul (k : ℕ) (g h : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    L.aut k (g * h) = (L.aut k g).comp (L.aut k h) := by
  apply (L.rep k _).1
  change (L.lev k).map (L.aut k (g * h)) = (L.lev k).map ((L.aut k g).comp (L.aut k h))
  rw [L.aut_spec, ← Level.map_map, L.aut_spec k h, Level.act_map, L.aut_spec k g, Level.act_mul]

theorem truncTensor_aut (k : ℕ) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}))
    (z : R.Trunc (k + 1) ⊗[R.A] L.Rm) :
    R.truncTensor L.Rm k (L.aut (k + 1) g z) = L.aut k g (R.truncTensor L.Rm k z) := by
  letI : Algebra (R.Trunc (k + 1)) (R.Trunc k ⊗[R.A] L.Rm) :=
    ((algebraMap (R.Trunc k) (R.Trunc k ⊗[R.A] L.Rm)).comp (R.truncMap k)).toAlgebra
  have hc : ∀ r : R.Trunc (k + 1),
      R.truncTensor L.Rm k (algebraMap (R.Trunc (k + 1)) (R.Trunc (k + 1) ⊗[R.A] L.Rm) r) =
        algebraMap (R.Trunc k) (R.Trunc k ⊗[R.A] L.Rm) (R.truncMap k r) := fun r => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rfl
  let φ₁ : R.Trunc (k + 1) ⊗[R.A] L.Rm →ₐ[R.Trunc (k + 1)] R.Trunc k ⊗[R.A] L.Rm :=
    { toRingHom := (R.truncTensor L.Rm k).toRingHom.comp (L.aut (k + 1) g).toRingHom
      commutes' := fun r => by
        change R.truncTensor L.Rm k (L.aut (k + 1) g (algebraMap _ _ r)) = _
        rw [AlgHom.commutes]
        exact hc r }
  let φ₂ : R.Trunc (k + 1) ⊗[R.A] L.Rm →ₐ[R.Trunc (k + 1)] R.Trunc k ⊗[R.A] L.Rm :=
    { toRingHom := (L.aut k g).toRingHom.comp (R.truncTensor L.Rm k).toRingHom
      commutes' := fun r => by
        change L.aut k g (R.truncTensor L.Rm k (algebraMap _ _ r)) = _
        rw [hc r, AlgHom.commutes]
        rfl }
  have key : φ₁ = φ₂ := by
    apply (L.rep (k + 1) (R.Trunc k ⊗[R.A] L.Rm)).1
    refine Level.ext (funext fun x => AlgHom.ext fun a => ?_)
    change R.truncTensor L.Rm k (L.aut (k + 1) g ((L.lev (k + 1)).α x a)) =
      L.aut k g (R.truncTensor L.Rm k ((L.lev (k + 1)).α x a))
    have h1 := congrArg (fun M => M.α x a) (L.aut_spec (k + 1) g)
    have h2 := congrArg (fun M => M.α x ((U.tr k).t.app m a)) (L.aut_spec k g)
    simp only [Level.map_α, Level.act_α, AlgHom.comp_apply] at h1 h2
    rw [h1, ← L.compat k _ a, ← L.compat k x a, h2]
  exact DFunLike.congr_fun key z

theorem succ_strictMono : StrictMono fun k : ℕ => k + 1 := fun _ _ h => Nat.succ_lt_succ h

def actTrunc (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (k : ℕ) :
    L.Rm →+* L.Rm ⧸ R.mapMax L.Rm ^ (k + 1) :=
  (R.truncQuot L.Rm k).symm.toRingHom.comp
    ((L.aut k g).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom))

theorem actTrunc_compat (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) {k : ℕ} :
    (Ideal.Quotient.factorPow (R.mapMax L.Rm) (succ_strictMono.monotone k.le_succ)).comp
      (L.actTrunc g (k + 1)) = L.actTrunc g k := by
  ext x
  change Ideal.Quotient.factorPow (R.mapMax L.Rm) (succ_strictMono.monotone k.le_succ)
      ((R.truncQuot L.Rm (k + 1)).symm (L.aut (k + 1) g ((1 : R.Trunc (k + 1)) ⊗ₜ[R.A] x))) =
    (R.truncQuot L.Rm k).symm (L.aut k g ((1 : R.Trunc k) ⊗ₜ[R.A] x))
  rw [← LocAlg.truncQuot_symm_truncTensor, L.truncTensor_aut, LocAlg.truncTensor_one_tmul]

def actRing (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) : L.Rm →+* L.Rm :=
  IsAdicComplete.StrictMono.liftRingHom (R.mapMax L.Rm) succ_strictMono (L.actTrunc g)
    (L.actTrunc_compat g)

theorem eq_of_tmul {x y : L.Rm}
    (h : ∀ k, (1 : R.Trunc k) ⊗ₜ[R.A] x = (1 : R.Trunc k) ⊗ₜ[R.A] y) : x = y := by
  have := IsHausdorff.StrictMono.funext' (R.mapMax L.Rm) succ_strictMono
    (f := fun _ : Unit => x) (g := fun _ => y) (fun k _ => by
      rw [← LocAlg.truncQuot_symm_tmul, ← LocAlg.truncQuot_symm_tmul, h k])
  exact congrFun this ()

theorem tmul_actRing (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (k : ℕ) (x : L.Rm) :
    (1 : R.Trunc k) ⊗ₜ[R.A] L.actRing g x = L.aut k g ((1 : R.Trunc k) ⊗ₜ[R.A] x) := by
  apply (R.truncQuot L.Rm k).symm.injective
  rw [LocAlg.truncQuot_symm_tmul]
  exact IsAdicComplete.StrictMono.mk_liftRingHom (R.mapMax L.Rm) succ_strictMono _ _ x

theorem actRing_one : L.actRing 1 = RingHom.id _ :=
  RingHom.ext fun x => L.eq_of_tmul fun k => by rw [L.tmul_actRing, L.aut_one]; rfl

theorem actRing_mul (g h : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    L.actRing (g * h) = (L.actRing g).comp (L.actRing h) :=
  RingHom.ext fun x => L.eq_of_tmul fun k => by
    rw [RingHom.comp_apply, L.tmul_actRing, L.tmul_actRing, L.tmul_actRing, L.aut_mul]
    rfl

theorem actRing_algebraMap (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (r : R.A) :
    L.actRing g (algebraMap R.A L.Rm r) = algebraMap R.A L.Rm r :=
  L.eq_of_tmul fun k => by
    rw [L.tmul_actRing]
    have e : (1 : R.Trunc k) ⊗ₜ[R.A] algebraMap R.A L.Rm r = algebraMap R.A (R.Trunc k ⊗[R.A] L.Rm) r :=
      Algebra.TensorProduct.includeRight.commutes r
    rw [e]
    exact ((L.aut k g).restrictScalars R.A).commutes r

def actEquiv : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}) →* (L.Rm ≃ₐ[R.A] L.Rm) where
  toFun g := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (L.actRing g) (L.actRing g⁻¹)
      (by rw [← L.actRing_mul, mul_inv_cancel, L.actRing_one])
      (by rw [← L.actRing_mul, inv_mul_cancel, L.actRing_one]))
    (L.actRing_algebraMap g)
  map_one' := AlgEquiv.ext fun x => by
    change L.actRing 1 x = x
    rw [L.actRing_one]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change L.actRing (g * h) x = L.actRing g (L.actRing h x)
    rw [L.actRing_mul]; rfl

instance mulSemiringAction : MulSemiringAction (GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) L.Rm :=
  MulSemiringAction.compHom L.Rm L.actEquiv

theorem smul_def (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (x : L.Rm) : g • x = L.actRing g x := by
  change L.actEquiv g x = _
  rfl

end LevelRep

end LevelRep

section Examples

variable (O Or : Type) [CommRing O] [CommRing Or] [IsLocalRing Or] [Algebra O Or]

example : IsArtinianRing (LocAlg.residueField (O := O) (Or := Or)).A :=
  inferInstanceAs (IsArtinianRing (ResidueField Or))

example (r : Or) : (LocAlg.residueField (O := O) (Or := Or)).red (residue Or r) = residue Or r :=

  LocAlg.red_algebraMap LocAlg.residueField r

example (p : ℕ) [Fact p.Prime] (S T : Type) [CommRing S] [Algebra O S] [CommRing T] [Algebra S T]
    (G : PDivGroup p S) (ι : PDivGroup.Action O G) (ϖ : O) (n m : ℕ) :
    MulAction (GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}))ᵐᵒᵖ (Level p G ι ϖ n m T) := inferInstance

example (p : ℕ) [Fact p.Prime] {Hb : GlobalTheory.VDiv.VarpiDivModule p O (ResidueField Or)} {R : LocAlg O Or}
    {U : ProRep p Hb R} {ϖ : O} {n m : ℕ} (L : LevelRep U ϖ n m) (x : L.Rm) :
    (1 : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) • x = L.actRing 1 x ∧ L.actRing 1 x = x :=
  ⟨L.smul_def 1 x, by rw [L.actRing_one]; rfl⟩

end Examples

end GlobalTheory.VDefo
