import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.CycleCountPf
open LateralTheory.DivDb

def CycSpec : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Disj y π p →
  ∃ l : Fin n → C, Function.Injective l ∧ ∀ j, y.charpoly.IsRoot (l j) ∧
    ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0

def FixScal : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)) (l : Fin n → C), Sys p → (∀ j, y * p j = p (π j) * y) → Deg n y →
  Disj y π p → Function.Injective l →
  (∀ j, ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0) →
  ∀ i, π i = i → ∃ c : C, y * p i = c • p i

theorem CycleCount_of (h1 : CycSpec) (h2 : FixScal) : CycleCount := by
  intro C _ _ _ N n p y π hp hy hyp hdeg hd
  obtain ⟨l, hl, hr⟩ := h1 C N n p y π hp hy hyp hd
  exact ⟨⟨l, hl, fun j => (hr j).1⟩, h2 C N n p y π l hp hyp hdeg hd hl (fun j => (hr j).2)⟩

end LateralTheory.DivDb.CycleCountPf
