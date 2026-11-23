import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gs1.Wt :
    ℕ → Type :=
    fun (n : ℕ) ↦ Fin n → ℝ

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gs1.FR :
    ℕ → Type :=
    fun (n : ℕ) ↦ AddMonoidAlgebra ℂ (UpperTheory.Reformulated.B.Gs1.Wt n)

theorem UpperTheory.Reformulated.B.Gs1.aux3 :
    ∀ {n : ℕ} (a : Fin n) (f : UpperTheory.Reformulated.B.Gs1.FR n) (x : UpperTheory.Reformulated.B.Gs1.Wt n),
      (↑(x a) : ℂ) * (f.coeff : UpperTheory.Reformulated.B.Gs1.Wt n → ℂ) x ≠ (0 : ℂ) → x ∈ f.coeff.support := by
  intro n a f x h
  exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h)

noncomputable def UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace :
    {n : ℕ} → Fin n → UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n :=
    fun {n : ℕ} (a : Fin n) (f : UpperTheory.Reformulated.B.Gs1.FR n) ↦
      AddMonoidAlgebra.ofCoeff
        (Finsupp.onFinset f.coeff.support
          (fun (x : UpperTheory.Reformulated.B.Gs1.Wt n) ↦ (↑(x a) : ℂ) * (f.coeff : UpperTheory.Reformulated.B.Gs1.Wt n → ℂ) x)
          (UpperTheory.Reformulated.B.Gs1.aux3 a f))

theorem UpperTheory.Reformulated.B.Gs1.aux5 :
    ∀ {n : ℕ} (a : Fin n) (f g : UpperTheory.Reformulated.B.Gs1.FR n),
      UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a (f + g) = UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a f + UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a g := by
  intro n a f g
  ext x
  simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, mul_add]

theorem UpperTheory.Reformulated.B.Gs1.aux6 :
    ∀ {n : ℕ} (a : Fin n) (c : ℂ) (f : UpperTheory.Reformulated.B.Gs1.FR n),
      UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a (c • f) = (RingHom.id ℂ : ℂ → ℂ) c • UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a f := by
  intro n a c f
  ext x
  simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, mul_left_comm]

noncomputable def UpperTheory.Reformulated.B.Gs1.lapD :
    {n : ℕ} → Fin n → UpperTheory.Reformulated.B.Gs1.FR n →ₗ[ℂ] UpperTheory.Reformulated.B.Gs1.FR n :=
    fun {n : ℕ} (a : Fin n) ↦
      { toFun := UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a, map_add' := UpperTheory.Reformulated.B.Gs1.aux5 a, map_smul' := UpperTheory.Reformulated.B.Gs1.aux6 a :
        UpperTheory.Reformulated.B.Gs1.FR n →ₗ[ℂ] UpperTheory.Reformulated.B.Gs1.FR n }

private theorem UpperTheory.Reformulated.B.Gs1.lapD_single {n : ℕ} (a : Fin n) (x : UpperTheory.Reformulated.B.Gs1.Wt n) (c : ℂ) :
    UpperTheory.Reformulated.B.Gs1.lapD a (AddMonoidAlgebra.single x c) =
      AddMonoidAlgebra.single x ((x a : ℂ) * c) := by
  classical
  change UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a _ = _
  ext y
  by_cases h : x = y
  · subst h
    simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace]
  · simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, Finsupp.single_apply, h]

theorem UpperTheory.Reformulated.B.Gs1.lapD_mul :
    ∀ {n : ℕ} (a : Fin n) (f g : UpperTheory.Reformulated.B.Gs1.FR n),
      (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) (f * g) =
        (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) f * g +
          f * (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) g := by
  intro n a f g
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, add_mul, add_mul]
    abel
  | single x c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, h₁, h₂, mul_add, mul_add]
      abel
    | single y d =>
      simp only [AddMonoidAlgebra.single_mul_single, UpperTheory.Reformulated.B.Gs1.lapD_single]
      rw [← AddMonoidAlgebra.single_add]
      congr 1
      simp only [Pi.add_apply, Complex.ofReal_add]
      ring
