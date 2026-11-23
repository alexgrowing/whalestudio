import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qj14.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qj14.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qj14.Hpk k r + UpperTheory.Reformulated.B.Qj14.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qj14.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qj14.UH (UpperTheory.Reformulated.B.Qj14.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qj14.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qj14.Mat k r → UpperTheory.Reformulated.B.Qj14.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qj14.cayley_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Y : Matrix ι ι ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [hinv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Qj14.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qj14.Mat k r},
      UpperTheory.Reformulated.B.Qj14.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qj14.kap Y ∈ UpperTheory.Reformulated.B.Qj14.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qj14.cayley_form (UpperTheory.Reformulated.B.Qj14.Hpk k r) Y h hu
