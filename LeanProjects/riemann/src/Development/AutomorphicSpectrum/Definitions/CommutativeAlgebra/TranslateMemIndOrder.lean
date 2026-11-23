import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

def prodSpan (A : Subalgebra R (T → R)) : Submodule R (T × T → R) :=
  Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z => a z.1 * b z.2}

structure IsHopfOrder (A : Subalgebra R (T → R)) : Prop where

  finite : Module.Finite R A

  projective : Module.Projective R A

  full : ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A

  comul : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A

  inv : ∀ f ∈ A, (fun x => f x⁻¹) ∈ A

def indOrder (ι : H →* T) (A : Subalgebra R (H → R)) : Subalgebra R (T → R) where
  carrier := {f | ∀ t, (fun h => f (t * ι h)) ∈ A}
  mul_mem' hf hg t := A.mul_mem (hf t) (hg t)
  add_mem' hf hg t := A.add_mem (hf t) (hg t)
  algebraMap_mem' r _ := A.algebraMap_mem r

def extOrder {R' : Type} [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) : Subalgebra R' (T → R') :=
  Algebra.adjoin R' {g | ∃ f ∈ A, g = fun t => φ (f t)}

def evalAt (A : Subalgebra R (T → R)) (t : T) : A →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : T => R) t).comp A.val

def augIdeal (A : Subalgebra R (T → R)) : Ideal A := RingHom.ker (evalAt A 1)

abbrev omega (A : Subalgebra R (T → R)) : Type := (augIdeal A).Cotangent

open Classical in

noncomputable def dlogChar (A : Subalgebra R (T → R)) (χ : T →* Rˣ) : omega A :=
  if h : (fun t => ((χ t : Rˣ) : R)) ∈ A then
    (augIdeal A).toCotangent ⟨⟨_, h⟩ - 1, by simp [augIdeal, evalAt, RingHom.mem_ker]⟩
  else 0

namespace OrderApi

omit [CommGroup T] in

theorem mul_mem_prodSpan {A : Subalgebra R (T → R)} {a b : T → R} (ha : a ∈ A) (hb : b ∈ A) :
    (fun z : T × T => a z.1 * b z.2) ∈ prodSpan A :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem mem_indOrder (ι : H →* T) (A : Subalgebra R (H → R)) (f : T → R) :
    f ∈ indOrder ι A ↔ ∀ t, (fun h => f (t * ι h)) ∈ A := Iff.rfl

omit [CommGroup T] in

theorem comp_mem_extOrder {R' : Type} [CommRing R'] (φ : R →+* R') {A : Subalgebra R (T → R)} {f : T → R}
    (hf : f ∈ A) : (fun t => φ (f t)) ∈ extOrder φ A :=
  Algebra.subset_adjoin ⟨f, hf, rfl⟩

theorem mem_augIdeal (A : Subalgebra R (T → R)) (f : A) : f ∈ augIdeal A ↔ (f : T → R) 1 = 0 := Iff.rfl

theorem dlogChar_of_mem (A : Subalgebra R (T → R)) (χ : T →* Rˣ) (h : (fun t => ((χ t : Rˣ) : R)) ∈ A) :
    dlogChar A χ =
      (augIdeal A).toCotangent ⟨⟨_, h⟩ - 1, by simp [augIdeal, evalAt, RingHom.mem_ker]⟩ := by
  rw [dlogChar, dif_pos h]

end OrderApi

namespace OrderEx

def muTwoOrder : Subalgebra ℤ (ℤˣ → ℤ) where
  carrier := {f | (2 : ℤ) ∣ f 1 - f (-1)}
  mul_mem' {f g} hf hg := by
    have : (f * g) 1 - (f * g) (-1) = f 1 * (g 1 - g (-1)) + (f 1 - f (-1)) * g (-1) := by
      simp only [Pi.mul_apply]; ring
    change (2 : ℤ) ∣ _
    rw [this]
    exact dvd_add (Dvd.dvd.mul_left hg _) (Dvd.dvd.mul_right hf _)
  add_mem' {f g} hf hg := by
    have : (f + g) 1 - (f + g) (-1) = (f 1 - f (-1)) + (g 1 - g (-1)) := by
      simp only [Pi.add_apply]; ring
    change (2 : ℤ) ∣ _
    rw [this]
    exact dvd_add hf hg
  algebraMap_mem' r := by
    change (2 : ℤ) ∣ _
    simp

example {S : Type} [CommRing S] {G : Type} [CommGroup G] (B : Subalgebra S (G → S)) : Module S (omega B) :=
  inferInstance

end OrderEx

end GlobalTheory.CompanionTheory.Ar.BT
