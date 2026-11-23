import Mathlib

open Finset

namespace GlobalTheory

theorem sum_eigenvectors_of_aeval_prod_linear_eq_zero :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ),
      Function.Injective ν →
      Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 →
      ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by
  intro N _ _ n Ω ν hν h w
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun s => s.elim0, fun s => s.elim0, ?_⟩
    have h1 : (1 : Module.End ℂ N) = 0 := by simpa using h
    have h2 : w = 0 := by
      have := congrArg (fun f : Module.End ℂ N => f w) h1
      simpa using this
    simp [h2]
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hinj : Set.InjOn (fun s => -ν s) (↑(Finset.univ : Finset (Fin n))) := by
      intro a _ b _ hab
      exact hν (neg_injective hab)
    have hsum := Lagrange.sum_basis hinj hne
    refine ⟨fun s => Polynomial.aeval (-Ω) (Lagrange.basis Finset.univ (fun s => -ν s) s) w, ?_, ?_⟩
    · intro s
      have key : (Polynomial.X + Polynomial.C (ν s)) * Lagrange.basis Finset.univ (fun s => -ν s) s
          = (∏ j ∈ Finset.univ.erase s, Polynomial.C ((-ν s - -ν j)⁻¹)) *
            ∏ s, (Polynomial.X + Polynomial.C (ν s)) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun s => Polynomial.X + Polynomial.C (ν s))
          (Finset.mem_univ s), Lagrange.basis]
        simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib, map_neg, sub_neg_eq_add]
        ring
      have h2 := congrArg (Polynomial.aeval (-Ω)) key
      rw [map_mul, map_mul, h, mul_zero] at h2
      have h3 := congrArg (fun f : Module.End ℂ N => f w) h2
      simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
        LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        LinearMap.zero_apply] at h3
      exact (neg_add_eq_zero.mp h3)
    · have h2 := congrArg (fun p => Polynomial.aeval (-Ω) p w) hsum
      simp only [map_sum, map_one, LinearMap.sum_apply, Module.End.one_apply] at h2
      exact h2.symm

end GlobalTheory
