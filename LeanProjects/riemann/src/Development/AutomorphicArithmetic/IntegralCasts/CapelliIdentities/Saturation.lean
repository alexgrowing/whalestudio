import Mathlib

noncomputable def UpperTheory.Reformulated.B.IdealSaturationByElement.sat :
    {R : Type} → [inst : CommRing R] → Ideal R → R → Ideal R :=
  fun {R} _ Q f =>
    { carrier := {g : R | ∃ n : ℕ, f ^ n * g ∈ Q}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : f ^ (m + n) * (a + b) = f ^ n * (f ^ m * a) + f ^ m * (f ^ n * b) := by ring
        rw [h]
        exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : f ^ n * (c • a) = c * (f ^ n * a) := by
          rw [smul_eq_mul]; ring
        rw [h]
        exact Q.mul_mem_left _ hn }
