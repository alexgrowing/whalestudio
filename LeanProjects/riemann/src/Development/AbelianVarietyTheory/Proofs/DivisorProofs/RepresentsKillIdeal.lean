import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PtClosed

def killIdeal {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop) :
    Ideal A where
  carrier := {a | ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f → f a = 0}
  add_mem' {a b} ha hb R' _ f hf := by rw [map_add, ha R' f hf, hb R' f hf, add_zero]
  zero_mem' R' _ f _ := map_zero f
  smul_mem' c a ha R' _ f hf := by rw [smul_eq_mul, map_mul, ha R' f hf, mul_zero]

def Represents {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop)
    (J : Ideal A) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f ↔ J ≤ RingHom.ker f

def ptQ {S : Scheme.{0}} (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop) (V : S.Opens)
    (hV : IsAffineOpen V) : ∀ (R' : Type) [CommRing R'], (Γ(S, V) →+* R') → Prop :=
  fun R' _ f ↦ P R' (spMap f ≫ hV.fromSpec)

theorem killIdeal_eq {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    killIdeal Q = J := by
  apply le_antisymm
  · intro a ha
    have := ha (A ⧸ J) (Ideal.Quotient.mk J) ((h _ _).2 (by simp [Ideal.mk_ker]))
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  · intro a ha R' _ f hf
    exact (h R' f).1 hf ha

theorem represents_killIdeal {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    Represents Q (killIdeal Q) := by
  rw [killIdeal_eq h]; exact h

theorem represents_restrict : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
  (U W : S.Opens) (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (J : Ideal Γ(S, U)),
  Represents (ptQ P U hU) J → Represents (ptQ P W hW) (J.map (S.presheaf.map (homOfLE h).op).hom) := by
  intro S P U W hU hW h J hJ R' _ f
  have e : spMap f ≫ hW.fromSpec =
      spMap (f.comp (S.presheaf.map (homOfLE h).op).hom) ≫ hU.fromSpec := by
    rw [← hU.map_fromSpec hW (homOfLE h).op]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap f ≫ hW.fromSpec) ↔ _
  rw [e, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed
