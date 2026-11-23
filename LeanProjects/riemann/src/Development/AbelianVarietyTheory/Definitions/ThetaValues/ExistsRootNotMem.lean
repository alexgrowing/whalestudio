import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure Fixes (c : Coeff l) (ta : c.F ≃+* c.F) : Prop where
  emb : ∀ (τ : E →+* ℂ) (a : E), ta (embF c τ a) = embF c τ a
  base : ∀ a : KA l, ta (IntermediateField.inclusion c.le a) = IntermediateField.inclusion c.le a

def Tw {K : Type} [Field K] (_ta : K ≃+* K) (S : Type) : Type := S

instance {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [h : CommRing S] : CommRing (Tw ta S) := h

instance {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] : Algebra K (Tw ta S) :=
  RingHom.toAlgebra (R := K) (S := S) ((algebraMap K S).comp ta.toRingHom)

def Tw.val {K : Type} [Field K] {ta : K ≃+* K} {S : Type} (s : Tw ta S) : S := s

theorem sOf_tw {ta : c.F ≃+* c.F} (h : Fixes c ta) (S : Type) [CommRing S] [Algebra c.F S] :
    sOf c (Tw ta S) = sOf c S := by
  unfold sOf
  congr 1
  ext a
  exact congrArg (algebraMap c.F S) (h.base a)

theorem isEigAt_tw {ta : c.F ≃+* c.F} (h : Fixes c ta) {S : Type} [CommRing S] [Algebra c.F S] (τ : E →+* ℂ)
    (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c (S := Tw ta S) τ v ↔ IsEigAt (Xo := Xo) c (S := S) τ v := by
  have e : ∀ a : 𝓞 E, algebraMap c.F (Tw ta S) (embK c τ a) = algebraMap c.F S (embK c τ a) :=
    fun a => congrArg (algebraMap c.F S) (h.emb τ a)
  unfold IsEigAt
  refine forall_congr' fun a => ?_
  rw [e a]
  rfl

def twPt {ta : c.F ≃+* c.F} (h : Fixes c ta) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrPt Xo c (Tw ta S) where
  x := y.x
  x_over := y.x_over.trans (sOf_tw h S).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_tw (S := S) h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_tw (S := S) h τ w).1 he)
  s := y.s
  gen := y.gen

def galRul {ta : c.F ≃+* c.F} (h : Fixes c ta) (f : Rul Xo c) : Rul Xo c :=
  fun p y => (evR Xo c f (twPt h y)).val

def covAut {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) : d.c₂.F ≃+* d.c₂.F :=
  (d.eF.symm.toRingEquiv.trans ta).trans d.eF.toRingEquiv

theorem fixes_refl : Fixes c (RingEquiv.refl c.F) := ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem Tw.val_algebraMap {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] (a : K) :
    (algebraMap K (Tw ta S) a).val = algebraMap K S (ta a) := rfl

theorem fixes_of_le {c c' : Coeff l} (ta : c'.F ≃+* c'.F)
    (h : ∀ x : c'.F, (x : ℂ) ∈ c.F → ta x = x) : Fixes c' ta :=
  ⟨fun τ a => h _ (c.conj τ a), fun a => h _ (c.le a.2)⟩

theorem galRul_smul {ta : c.F ≃+* c.F} (h : Fixes c ta) (a : c.F) (f : Rul Xo c) :
    galRul h (a • f) = ta a • galRul h f := by
  funext p y
  show (evR Xo c (a • f) (twPt h y)).val = ta a • (evR Xo c f (twPt h y)).val
  unfold evR
  rw [evalAt_smul, Algebra.smul_def]
  rfl

theorem covAut_apply_eF {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) (a : c.F) :
    covAut d ta (d.eF a) = d.eF (ta a) := by
  show d.eF (ta (d.eF.symm (d.eF a))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem fixes_covAut {n : ℕ} (d : DeltaDat Xo c n) (hA : d.l₂.A = 1) {ta : c.F ≃+* c.F} (h : Fixes c ta) :
    Fixes d.c₂ (covAut d ta) := by
  have key : ∀ (x : d.c₂.F), ta (d.eF.symm x) = d.eF.symm x → covAut d ta x = x := fun x hx => by
    show d.eF (ta (d.eF.symm x)) = x
    rw [hx, AlgEquiv.apply_symm_apply]
  refine ⟨fun τ a => key _ (h.emb τ a), fun a => key _ ?_⟩
  have hle : KA d.l₂ ≤ KA l := by
    unfold KA
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact IntermediateField.subset_adjoin _ _ (by simp)
    · have : zeta d.l₂.A = 1 := by rw [hA]; simp [zeta]
      rw [this]; exact one_mem _
  exact h.base ⟨a, hle a.2⟩

example {ta : c.F ≃+* c.F} (h : Fixes c ta) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    (twPt h y).x = y.x := rfl

example : (algebraMap ℂ (Tw Complex.conjAe.toRingEquiv ℂ) Complex.I).val = -Complex.I := by
  rw [Tw.val_algebraMap]
  simp

end GlobalTheory.GalTw
