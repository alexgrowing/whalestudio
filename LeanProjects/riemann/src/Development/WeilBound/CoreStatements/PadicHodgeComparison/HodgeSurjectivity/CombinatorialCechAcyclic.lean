import Mathlib

set_option autoImplicit false

noncomputable section

namespace CechCochains.H4

variable {d : ℕ} (M : Type) [AddCommGroup M]

def sgn (I : Finset (Fin d)) (i : Fin d) : ℤ := (-1) ^ (I.filter (· < i)).card

def Coch (T : Finset (Fin d)) (p : ℕ) : Type := {I : Finset (Fin d) // T ⊆ I ∧ I.card = p + 1} → M

instance (T : Finset (Fin d)) (p : ℕ) : AddCommGroup (Coch M T p) := inferInstanceAs (AddCommGroup (_ → M))

def delta (T : Finset (Fin d)) (p : ℕ) (c : Coch M T p) : Coch M T (p + 1) := fun I =>
  ∑ i ∈ I.1, if h : T ⊆ I.1.erase i ∧ (I.1.erase i).card = p + 1 then sgn I.1 i • c ⟨I.1.erase i, h⟩ else 0

def CombinatorialCechAcyclic : Prop :=
  ∀ (d : ℕ) (M : Type) [AddCommGroup M] (T : Finset (Fin d)), T.Nonempty → T ≠ Finset.univ →
    (∀ c : Coch M T 0, delta M T 0 c = 0 → c = 0) ∧
    ∀ (p : ℕ) (c : Coch M T (p + 1)), delta M T (p + 1) c = 0 → ∃ b : Coch M T p, delta M T p b = c

def CombEmpty : Prop :=
  ∀ (d : ℕ) (M : Type) [AddCommGroup M], 0 < d →
    (∀ c : Coch M (∅ : Finset (Fin d)) 0, delta M (∅ : Finset (Fin d)) 0 c = 0 → ∃ m : M, ∀ I, c I = m) ∧
    ∀ (p : ℕ) (c : Coch M (∅ : Finset (Fin d)) (p + 1)), delta M (∅ : Finset (Fin d)) (p + 1) c = 0 → ∃ b : Coch M (∅ : Finset (Fin d)) p, delta M (∅ : Finset (Fin d)) p b = c

end CechCochains.H4
