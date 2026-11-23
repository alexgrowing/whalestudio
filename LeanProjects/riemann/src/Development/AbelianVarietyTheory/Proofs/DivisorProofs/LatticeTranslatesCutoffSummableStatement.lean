import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeTranslatesCutoffSummable
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_translates_cutoff_summable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h (x + l) * f x) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  first | exact @GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate | exact GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate | (intros; apply GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate <;> assumption)
