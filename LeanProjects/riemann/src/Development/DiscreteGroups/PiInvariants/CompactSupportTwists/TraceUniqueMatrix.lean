import Mathlib

namespace DiscreteGroups.T1.Desc.TraceUniqueU3

open Matrix

theorem trace_unique_matrix {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hg : ∀ A B, g (A * B) = g (B * A)) :
    ∃ c : ℂ, ∀ A, g A = c * A.trace := by
  classical
  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.mk₂ ℂ (fun C A => (A * C).trace)
      (fun C C' A => by simp only [Matrix.mul_add, Matrix.trace_add])
      (fun c C A => by simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul])
      (fun C A A' => by simp only [Matrix.add_mul, Matrix.trace_add])
      (fun c C A => by simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul])
  have hΦ : ∀ C A, Φ C A = (A * C).trace := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    intro C C' h
    rw [Matrix.ext_iff_trace_mul_left]
    intro X
    have h1 := LinearMap.congr_fun h X
    rw [hΦ, hΦ] at h1
    exact h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨C, hC⟩ := hsurj g
  have hgC : ∀ A, g A = (A * C).trace := fun A => by rw [← hC, hΦ]
  have hcomm : ∀ B, B * C = C * B := by
    intro B
    rw [Matrix.ext_iff_trace_mul_left]
    intro A
    calc (A * (B * C)).trace = (A * B * C).trace := by rw [Matrix.mul_assoc]
      _ = g (A * B) := (hgC _).symm
      _ = g (B * A) := hg A B
      _ = (B * A * C).trace := hgC _
      _ = (A * C * B).trace := (Matrix.trace_mul_cycle A C B).symm
      _ = (A * (C * B)).trace := by rw [Matrix.mul_assoc]
  have hcen : C ∈ Subalgebra.center ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Subalgebra.mem_center_iff]
    exact hcomm
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (Algebra.IsCentral.out hcen)
  refine ⟨c, fun A => ?_⟩
  rw [hgC, ← hc, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul]

end DiscreteGroups.T1.Desc.TraceUniqueU3
