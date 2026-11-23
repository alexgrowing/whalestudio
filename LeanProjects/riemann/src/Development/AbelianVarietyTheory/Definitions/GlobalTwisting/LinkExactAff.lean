import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

noncomputable section

open scoped Matrix

namespace GlobalTheory.SeqCx

def uniM (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Set (List M) :=
  {l | ∃ f : Fin l.length → M →ₗ[R] R, ∀ i j : Fin l.length, f i (l.get j) = if i = j then 1 else 0}

def low (R : Type) [CommRing R] (n : ℕ) : Set (ℕ →₀ R) := {x | ∀ i, n ≤ i → x i = 0}

def aff (R : Type) [CommRing R] (n j : ℕ) : Set (ℕ →₀ R) := {x | x - Finsupp.single j 1 ∈ low R n}

def LinkExactLow (R : Type) [CommRing R] (s n : ℕ) : Prop :=
  ∀ τ ∈ uniM R (ℕ →₀ R), ∀ p : ℕ, p + s + τ.length ≤ n → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n) τ) p

def LinkExactAff (R : Type) [CommRing R] (s n : ℕ) : Prop :=
  ∀ j : ℕ, n ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ p : ℕ, p + s + τ.length ≤ n + 1 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) τ) p

def hbd (V W : Type) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z : List V × List W =>
    Finsupp.mapDomain (fun x => (x, z.2)) (bd V (Finsupp.single z.1 1))

def vbd (V W : Type) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z : List V × List W =>
    Finsupp.mapDomain (fun w => (z.1, w)) (bd W (Finsupp.single z.2 1))

def chains2 {V W : Type} (D : Set (List V × List W)) (a b : ℕ) : Submodule ℤ (List V × List W →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {z | z ∈ D ∧ z.1.length = a ∧ z.2.length = b}

def SubClosed2 {V W : Type} (D : Set (List V × List W)) : Prop :=
  ∀ z ∈ D, ∀ (x : List V) (w : List W), x.Sublist z.1 → w.Sublist z.2 → (x, w) ∈ D

def splitPairs (R : Type) [CommRing R] (n : ℕ) : Set (List ((Fin n → R) × (Fin n → R)) × List (Fin n → R)) :=
  {z | z.1 ∈ splitSeq R n ∧ z.2 ∈ uniSeq R n ∧ ∀ y ∈ z.1, ∀ u ∈ z.2, y.2 ⬝ᵥ u = 0}

example : [Finsupp.single 0 (1 : ℤ)] ∈ uniM ℤ (ℕ →₀ ℤ) := by
  refine ⟨fun _ => Finsupp.lapply 0, fun i j => ?_⟩
  obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
  fin_cases i
  simp

end GlobalTheory.SeqCx

end
