import Mathlib
open NumberField

noncomputable section
namespace GlobalTheory

theorem norm_ratCast_padicComplex (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ‖(q : ℂ_[p])‖ = padicNorm p q := by
  have h := PadicComplex.norm_extends' p (q : ℚ_[p])
  rw [Padic.eq_padicNorm] at h
  rw [← h]
  congr 1
  rw [map_ratCast]
  exact (map_ratCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) q).symm

theorem sum_log_norm_embeddings_padicComplex (K : Type) [Field K] [NumberField K] (p : ℕ)
    [Fact p.Prime] (a : K) (ha : a ≠ 0) :
    ∑ᶠ j : K →+* ℂ_[p], Real.log ‖j a‖ = -((padicValRat p (Algebra.norm ℚ a) : ℝ) * Real.log p) := by
  classical
  have hN : Algebra.norm ℚ a ≠ 0 := (Algebra.norm_ne_zero_iff).2 ha
  rw [finsum_eq_sum_of_fintype]
  have hsum : ∑ j : K →+* ℂ_[p], Real.log ‖j a‖ = ∑ σ : K →ₐ[ℚ] ℂ_[p], Real.log ‖σ a‖ := by
    refine Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ_[p]) _ _ (fun j => rfl)
  rw [hsum, ← Real.log_prod (fun σ _ => (norm_ne_zero_iff.2 ((map_ne_zero σ).2 ha))), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] a]
  have : (algebraMap ℚ ℂ_[p]) (Algebra.norm ℚ a) = ((Algebra.norm ℚ a : ℚ) : ℂ_[p]) := by simp
  rw [this, norm_ratCast_padicComplex, padicNorm.eq_zpow_of_nonzero hN]
  push_cast
  rw [Real.log_zpow]
  push_cast
  ring

end GlobalTheory
