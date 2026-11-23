import Mathlib

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

def pair (f x : Fin r → k) : k := ∑ i, f i * x i

def opU (ψ : (Fin r → k) → R) (f : Fin r → k) : R :=
  ∑ x ∈ univ.filter (fun x => pair f x = 1), ψ x

def opD (φ : (Fin r → k) → R) (x : Fin r → k) : R :=
  ∑ f ∈ univ.filter (fun f => pair f x = 1), φ f

def diaP (c : kˣ) (φ : (Fin r → k) → R) (f : Fin r → k) : R := φ ((c : k) • f)

def diaV (c : kˣ) (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ψ (((c⁻¹ : kˣ) : k) • x)

def nmP (φ : (Fin r → k) → R) (f : Fin r → k) : R := ∑ c : kˣ, diaP c φ f

def nmV (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ∑ c : kˣ, diaV c ψ x

def trV (ψ : (Fin r → k) → R) : R := ∑ x ∈ univ.filter (fun x => x ≠ 0), ψ x

def trP (φ : (Fin r → k) → R) : R := ∑ f ∈ univ.filter (fun f => f ≠ 0), φ f

end Ops

def AdjointReformulated : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R]
    (ψ φ : (Fin r → k) → R),
    ∑ f, opU ψ f * φ f = ∑ x, ψ x * opD φ x

def DualCompositionReformulated : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R],
    2 ≤ r → ∀ (ψ : (Fin r → k) → R) (x : Fin r → k), x ≠ 0 →
      opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x
        - ((Fintype.card k : R)) ^ (r - 2) * nmV ψ x + ((Fintype.card k : R)) ^ (r - 2) * trV ψ

def CompositionWithDual : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R],
    2 ≤ r → ∀ (φ : (Fin r → k) → R) (f : Fin r → k), f ≠ 0 →
      opU (opD φ) f = ((Fintype.card k : R)) ^ (r - 1) * φ f
        - ((Fintype.card k : R)) ^ (r - 2) * nmP φ f + ((Fintype.card k : R)) ^ (r - 2) * trP φ

def EquivarianceReformulated : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R] (c : kˣ),
    (∀ ψ : (Fin r → k) → R, opU (diaV c ψ) = diaP c (opU ψ)) ∧
    (∀ φ : (Fin r → k) → R, opD (diaP c φ) = diaV c (opD φ))

def UnitsSumZero : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (R : Type) [CommRing R],
    (∀ ψ : (Fin r → k) → R, (∀ y, y ≠ 0 → nmV ψ y = 0) →
      (∀ f, nmP (opU ψ) f = 0) ∧ trV ψ = 0 ∧
      (2 ≤ r → ∀ x, x ≠ 0 → opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x)) ∧
    (∀ φ : (Fin r → k) → R, (∀ f, f ≠ 0 → nmP φ f = 0) →
      (∀ x, nmV (opD φ) x = 0) ∧ trP φ = 0 ∧
      (2 ≤ r → ∀ f, f ≠ 0 → opU (opD φ) f = ((Fintype.card k : R)) ^ (r - 1) * φ f))

def ramSub (ι H X K : Type) [DecidableEq ι] [Group H] [Fintype H] [MulAction (ι → H) X] [Field K] :
    Submodule K (X → K) where
  carrier := {φ | ∀ (v : ι) (x : X), ∑ c : H, φ ((Pi.mulSingle v c : ι → H) • x) = 0}
  add_mem' := fun {a b} ha hb v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    have h2 : ∑ c : H, b ((Pi.mulSingle v c : ι → H) • x) = 0 := hb v x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h1, h2, add_zero]
  zero_mem' := fun v x => by simp
  smul_mem' := fun s a ha v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h1, mul_zero]

def FinrankFiberSumZero : Prop :=
  ∀ (ι H X K : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] [Field K],
    (∀ (g : ι → H) (x : X), g • x = x → g = 1) →
    Module.finrank K (ramSub ι H X K) * Fintype.card H ^ Fintype.card ι =
      Fintype.card X * (Fintype.card H - 1) ^ Fintype.card ι

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
