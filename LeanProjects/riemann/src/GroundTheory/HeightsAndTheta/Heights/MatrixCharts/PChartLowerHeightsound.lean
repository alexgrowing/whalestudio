import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace ChartLowerBlockBound

theorem period_apply_of_le (D : PeriodChartData) (T : ToricBlock D) (z : Fin D.n → ℂ)
    (ℓ : Fin D.a → ℂ) (i l : Fin D.g) (h : T.r ≤ i.val) :
    D.period z ℓ i l = D.τ0 z i l := by
  simp [PeriodChartData.period, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, T.support _ i l (Or.inl h)]

theorem entry_bound (D : PeriodChartData) (i l : Fin D.g) :
    ∃ C : ℝ, ∀ p ∈ D.K, ‖D.τ0 p.1 i l‖ ≤ C := by
  have hc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  have hcont : ContinuousOn (fun z => D.τ0 z i l) (Prod.fst '' D.K) :=
    ((D.τ0_analytic i l).continuousOn).mono hsub
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  exact ⟨C, fun p hp => hC p.1 ⟨p, hp, rfl⟩⟩

end ChartLowerBlockBound

theorem ChartLowerBlockBound.proof : ChartLowerBlockBound.Statement := by
  intro D T
  choose C hC using ChartLowerBlockBound.entry_bound D
  refine ⟨1 + ∑ i, ∑ l, |C i l|, ?_, ?_⟩
  · have : 0 ≤ ∑ i, ∑ l, |C i l| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · intro p hp ℓ i l hi
    rw [ChartLowerBlockBound.period_apply_of_le D T p.1 ℓ i l hi]
    have h1 : |C i l| ≤ ∑ l', |C i l'| :=
      Finset.single_le_sum (f := fun l' => |C i l'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have h2 : ∑ l', |C i l'| ≤ ∑ i', ∑ l', |C i' l'| :=
      Finset.single_le_sum (f := fun i' => ∑ l', |C i' l'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := hC i l p hp
    have h4 := le_abs_self (C i l)
    linarith

end

end GroundTheory.Heights₂.Heights
