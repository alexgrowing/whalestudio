import Mathlib

namespace GlobalTheory.SequenceFromIteration

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hstep : ∀ (n : ℕ) (a : A), P n a → ∃ b : A, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n : ℕ, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  choose g hgP hgQ using hstep
  let G : (n : ℕ) → {a : A // P n a} := fun n =>
    Nat.rec (motive := fun n => {a : A // P n a}) ⟨a₀, h₀⟩
      (fun k x => ⟨g k x.1 x.2, hgP k x.1 x.2⟩) n
  exact ⟨fun n => (G n).1, rfl, fun n => ⟨(G n).2, hgQ n (G n).1 (G n).2⟩⟩

end GlobalTheory.SequenceFromIteration
