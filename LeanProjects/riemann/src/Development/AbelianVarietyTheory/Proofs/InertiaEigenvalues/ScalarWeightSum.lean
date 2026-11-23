import Mathlib

namespace GlobalTheory.WeightSum

theorem scalar_weight_sum {ι : Type} (S : Finset ι) (w : ι → ℤ) (a : ι → ℂ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ∑ s ∈ S, z ^ w s * a s = 0) :
    ∑ s ∈ S, (w s : ℂ) * a s = 0 := by
  have hG : HasDerivAt (fun u : ℂ => ∑ s ∈ S, Complex.exp ((w s : ℂ) * (u * Complex.I)) * a s)
      (∑ s ∈ S, ((w s : ℂ) * Complex.I) * a s) ((0 : ℝ) : ℂ) := by
    apply HasDerivAt.fun_sum
    intro s _
    have h1 : HasDerivAt (fun u : ℂ => (w s : ℂ) * (u * Complex.I)) ((w s : ℂ) * Complex.I)
        ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const Complex.I).const_mul (w s : ℂ)
    have h2 := h1.cexp.mul_const (a s)
    simpa using h2
  have hg := hG.comp_ofReal
  have hz : (fun t : ℝ => ∑ s ∈ S, Complex.exp ((w s : ℂ) * ((t : ℂ) * Complex.I)) * a s)
      = fun _ => (0 : ℂ) := by
    funext t
    have := h (Complex.exp (t * Complex.I)) (Complex.norm_exp_ofReal_mul_I t)
    simpa only [← Complex.exp_int_mul] using this
  rw [hz] at hg
  have h0 := hg.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  have h3 : (∑ s ∈ S, (w s : ℂ) * a s) * Complex.I = 0 := by
    rw [← h0, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact (mul_eq_zero.mp h3).resolve_right Complex.I_ne_zero

theorem weight_sum_mem {E : Type} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E) {ι : Type}
    (S : Finset ι) (w : ι → ℤ) (f : ι → E)
    (h : ∀ z : ℂ, ‖z‖ = (1 : ℝ) → ∑ s ∈ S, z ^ w s • f s ∈ V) :
    ∑ s ∈ S, ((w s : ℤ) : ℂ) • f s ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have := scalar_weight_sum S w (fun s => φ (f s)) fun z hz => by
    simpa [map_sum] using hφ _ (h z hz)
  simpa [map_sum] using this

end GlobalTheory.WeightSum
