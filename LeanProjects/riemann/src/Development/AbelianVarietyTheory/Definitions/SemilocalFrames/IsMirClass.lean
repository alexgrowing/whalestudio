import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

namespace GlobalTheory.GLm

open Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def InMir {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (i : ℕ) + 1 = n → M i j = (1 : Mt g n) i j

def IsMirClass {n : ℕ} (F : Gn g n → ℂ) : Prop :=
  ∀ p x : Gn g n, InMir (p : Mt g n) → InMir (x : Mt g n) → F (p * x * p⁻¹) = F x

def InR (i : ℕ) {n : ℕ} (M : Mt g n) : Prop := InPar i M ∧ IsUniUp (br i (n - i) M)

def supFrom (i : ℕ) {n : ℕ} (M : Mt g n) : ZMod g := ∑ j ∈ Finset.Ico i (n - 1), entN M j (j + 1)

def diag1 {k : ℕ} (h : Gn g k) (n : ℕ) : Gn g n :=
  toG fun i j : Fin n => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (h : Mt g k) i j else (1 : Mt g n) i j

def tail (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (F : Gn g n → ℂ) : Gn g m → ℂ := fun p =>
  ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹ * ∑ x : Gn g n,
    if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
      F x * (ψ₀ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0

def indR (ψ₀ : AddChar (ZMod g) ℂ) (i n : ℕ) (ρ : Gn g i → ℂ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InR i (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InMir (y : Mt g n) ∧ InR i ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ρ (toG (tl i ((y⁻¹ * x * y : Gn g n) : Mt g n))) * ψ₀ (supFrom i ((y⁻¹ * x * y : Gn g n) : Mt g n)) else 0

def indV (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) : Gn g (m + 1) → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1)))).card : ℂ)⁻¹ *
    ∑ y : Gn g (m + 1), if InMir (y : Mt g (m + 1)) ∧ InMir ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) ∧
        InMir (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1))) then
      f (toG (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)))) *
        ψ₀ (entN ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) (m - 1) m) else 0

def InPat {N : ℕ} (Φ : Fin N → Fin N → Prop) (M : Mt g N) : Prop := ∀ a b, ¬ Φ a b → M a b = (1 : Mt g N) a b

def sumAt {N : ℕ} (E : Fin N → Fin N → Prop) (M : Mt g N) : ZMod g := ∑ a, ∑ b, if E a b then M a b else 0

def ePat (g N : ℕ) [Fact g.Prime] (Φ E : Fin N → Fin N → Prop) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (Gn g N) :=
  eDat g N (InPat Φ) (sumAt E) ψ₀

def IsW (k s a : ℕ) : Prop := s ≤ a ∧ a < s + k

def phI (k s i : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  (IsW k s a ∧ IsW k s b ∧ a < b) ∨ (¬ IsW k s a ∧ ¬ IsW k s b ∧ a < b) ∨ ((a : ℕ) < i ∧ IsW k s b) ∨
    (IsW k s a ∧ ((i < (b : ℕ) ∧ (b : ℕ) < s) ∨ ((b : ℕ) = s + k ∧ i < s) ∨ s + k < (b : ℕ)))

def eeI (k s : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  ((b : ℕ) = a + 1 ∧ (b : ℕ) < s) ∨ ((a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) ∨ ((b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ)) ∨
    ((b : ℕ) = a + 1 ∧ IsW k s a ∧ IsW k s b)

def pm (g : ℕ) [Fact g.Prime] {n : ℕ} (σ : Equiv.Perm (Fin n)) : Gn g n :=
  toG fun r j : Fin n => if r = σ j then 1 else 0

def sigI (a c i j : ℕ) : ℕ := if j < i then j else if j < a then c + (j - i) else if j < a + (c - i) then i + (j - a) else j

def wI (g : ℕ) [Fact g.Prime] (a c i n : ℕ) : Gn g n :=
  toG fun r j : Fin n => if (r : ℕ) = sigI a c i j then 1 else 0

def mean {G : Type} [Fintype G] (f : G → ℂ) : ℂ := (Fintype.card G : ℂ)⁻¹ * ∑ x, f x

theorem inMir_one (n : ℕ) : InMir (1 : Mt g n) := fun _ _ _ => rfl

end GlobalTheory.GLm
