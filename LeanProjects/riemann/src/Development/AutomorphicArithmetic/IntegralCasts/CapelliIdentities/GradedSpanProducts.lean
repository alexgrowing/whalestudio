import Mathlib

noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan.{u_1} :
    {Ω : Type u_1} → [inst : CommRing Ω] → {q r : ℕ} → (Fin q → Ω) → (Fin r → ℕ) → (Fin r → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type u_1} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) ↦
      AddSubgroup.closure
        {x : Ω | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j : Fin q, μ j = n ∧ x = t l * ∏ j : Fin q, w j ^ μ j}

@[reducible] noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.pc :
    {Ω : Type} → [inst : Field Ω] → {q : ℕ} → (Fin q → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω) (n : ℕ) ↦
      UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan w (fun (x : Fin (1 : ℕ)) ↦ (0 : ℕ)) (fun (x : Fin (1 : ℕ)) ↦ (1 : Ω)) n

theorem UpperTheory.Reformulated.B.GradedSpanProducts.pc_mul :
    ∀ {Ω : Type} [inst : Field Ω] {q : ℕ} (w : Fin q → Ω) {a b : ℕ} {x z : Ω},
      x ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w a → z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w b → x * z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w (a + b) := by
  intro Ω _ q w a b x z hx hz
  unfold UpperTheory.Reformulated.B.GradedSpanProducts.pc UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan at *
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, μ, hμ, rfl⟩ := hx
      obtain ⟨_, ν, hν, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨l, fun j => μ j + ν j, ?_, ?_⟩
      · simp only [zero_add] at hμ hν ⊢
        rw [Finset.sum_add_distrib, hμ, hν]
      · simp only [one_mul, pow_add, Finset.prod_mul_distrib]
    | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
    | neg z _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h
  | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | neg x _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
