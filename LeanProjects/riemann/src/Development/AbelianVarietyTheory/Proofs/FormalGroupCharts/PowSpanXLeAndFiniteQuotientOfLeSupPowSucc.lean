import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (I : Ideal (MvPowerSeries σ k)) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ (M + 1) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ∧ Module.Finite k (MvPowerSeries σ k ⧸ I) := by
  intro k _ σ _ I M h
  set m : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range MvPowerSeries.X) with hm
  have hfg : m.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hle : m ^ M ≤ I := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (N' := m ^ M) (N := I) (I := m)
      (Ideal.FG.pow hfg) hjac ?_
    rw [pow_succ'] at h
    exact h
  exact ⟨hle, FormalIsogeny.finite_quotient_of_pow_le (N := M) hle⟩

end GlobalTheory
