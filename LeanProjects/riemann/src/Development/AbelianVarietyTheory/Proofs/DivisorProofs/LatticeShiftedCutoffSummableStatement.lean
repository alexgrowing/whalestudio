import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeShiftedCutoffSummable
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_shifted_cutoff_summable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  first | exact @GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub | exact GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub | (intros; apply GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub <;> assumption)
