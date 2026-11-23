import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}}

def htAct {s : S ⟶ Sp R} (o : Obj b N s) : Out.RingAct o.A D.O :=
  ⟨o.act.act, o.act.hom, o.act.one, o.act.mul, o.act.add⟩

@[simp] theorem htAct_act {s : S ⟶ Sp R} (o : Obj b N s) (c : D.O) : (htAct o).act c = o.act.act c := rfl

abbrev HTIw {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) : Type 1 :=
  Chain (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) (Ideal.absNorm w ^ D.m) D.n

def HTIwMap {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {w : Ideal (𝓞 D.F)}
    (C' : HTIw o' w) (C : HTIw o w) (f : S' ⟶ S) : Prop :=
  ∃ m : ObjMap o' o f, Nonempty (ChainMap C' C f m.φ)

theorem HTIw.exists_pull {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {w : Ideal (𝓞 D.F)} (C : HTIw o w) {f : S' ⟶ S} (m : ObjMap o' o f) :
    ∃ C' : HTIw o' w, HTIwMap C' C f := by
  obtain ⟨C', ⟨e⟩⟩ := Chain.exists_pull (ρ' := htAct o') C m.cart m.act
  exact ⟨C', m, ⟨e⟩⟩

theorem HTIwMap.subsingleton {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {w : Ideal (𝓞 D.F)} (C' : HTIw o' w) (C : HTIw o w) (f : S' ⟶ S) (m : ObjMap o' o f) :
    Subsingleton (ChainMap C' C f m.φ) := inferInstance

def IsPlaceOf (b : Base D R) (i : Fin D.a) (w : Ideal (𝓞 D.F)) : Prop :=
  w.IsMaximal ∧ ((p : 𝓞 D.F) ∈ w) ∧
    ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k), RingHom.ker (β.comp (b.t i)) = w

structure HTIwRep (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) where

  X : Scheme.{0}

  s : X ⟶ Sp R

  univ : Obj b N s

  univC : HTIw univ w

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s') (C : HTIw o w),
    ∃! f : S ⟶ X, f ≫ s = s' ∧ HTIwMap C univC f

section Basic₂

example {s : S ⟶ Sp R} {o : Obj b N s} {w : Ideal (𝓞 D.F)} (C : HTIw o w) :
    IsIsogDeg (C.π (Fin.last D.n)) (Ideal.absNorm w ^ (D.m * D.n)) := by
  rw [pow_mul]; simpa using C.π_deg (Fin.last D.n)

example {s : S ⟶ Sp R} {o : Obj b N s} {w : Ideal (𝓞 D.F)} (C : HTIw o w) {T : Over S} (x : T ⟶ o.A)
    (h : x ≫ C.π (Fin.last D.n) = 1) (c : 𝓞 D.F) (hc : c ∈ w) : x ≫ o.act.act (algebraMap _ _ c) = 1 :=
  (C.ker_last T x).1 h _ (Ideal.mem_map_of_mem _ hc)

example {s : S ⟶ Sp R} {o : Obj b N s} {w : Ideal (𝓞 D.F)} (C : HTIw o w) (i : Fin (D.n + 1)) (c : 𝓞 D.F)
    (hc : c ∈ w) : ∃ g : C.B i ⟶ o.A, C.π i ≫ g = o.act.act (algebraMap _ _ c) :=
  (C.existsUnique_close i (Ideal.mem_map_of_mem _ hc)).exists

end Basic₂

end GlobalTheory.IwLevel
