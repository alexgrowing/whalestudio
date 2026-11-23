import Mathlib

theorem UpperTheory.Reformulated.B.Yhd5.main :
    ∀ {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ},
      (∀ i ∈ u, DifferentiableOn ℂ (f i) U) → DifferentiableOn ℂ (fun (t : Fin n → ℂ) ↦ ∏ i ∈ u, f i t) U := by
  intro n U ι u f h
  classical
  induction u using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    have h1 : DifferentiableOn ℂ (f a) U := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha]
    exact h1.mul h2
