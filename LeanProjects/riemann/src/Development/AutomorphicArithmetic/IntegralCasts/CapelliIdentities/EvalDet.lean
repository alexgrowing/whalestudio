import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi25.UG :
    ℕ → Type :=
    fun (N : ℕ) ↦ ↥(Matrix.unitaryGroup (Fin N) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qi25.ent :
    {N : ℕ} → UpperTheory.Reformulated.B.Qi25.UG N → Fin N × Fin N → ℂ :=
    fun {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) (ij : Fin N × Fin N) ↦ (↑g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

noncomputable def UpperTheory.Reformulated.B.Qi25.IsPD :
    {N : ℕ} → (UpperTheory.Reformulated.B.Qi25.UG N → ℂ) → Prop :=
    fun {N : ℕ} (f : UpperTheory.Reformulated.B.Qi25.UG N → ℂ) ↦
      ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
        ∀ (g : UpperTheory.Reformulated.B.Qi25.UG N),
          f g * (↑g : Matrix (Fin N) (Fin N) ℂ).det ^ k =
            (MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g) : MvPolynomial (Fin N × Fin N) ℂ → ℂ) P

private theorem UpperTheory.Reformulated.B.Qi25.eval_det {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) :
    MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g)
        (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det =
      (↑g : Matrix (Fin N) (Fin N) ℂ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [UpperTheory.Reformulated.B.Qi25.ent]

theorem UpperTheory.Reformulated.B.Qi25.sum.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by
  intro N ι s F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, 0, fun g ↦ by simp⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨k, P, hP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨l, Q, hQ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨k + l,
      P * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ l
        + Q * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ k,
      fun g ↦ ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, UpperTheory.Reformulated.B.Qi25.eval_det, ← hP g, ← hQ g]
    simp only [Finset.sum_insert ha]
    ring
