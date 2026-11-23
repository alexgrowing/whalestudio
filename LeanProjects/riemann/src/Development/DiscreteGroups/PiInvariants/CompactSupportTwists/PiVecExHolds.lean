import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CuspPairD

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

theorem piVecEx_holds : PiVecEx := by
  intro E _ _ _ n hn D π hθ ψ hψ u hu hus
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have hψc : IsCuspForm ψ := π.cusp ψ hψ
  have hA : ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g := hθ.1 ψ hψ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ s, u s ≠ 0 → |s| ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hus.isCompact.isBounded
    exact ⟨R, fun s hs => by
      have := hR (subset_tsupport u hs)
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this⟩
  obtain ⟨U, hU⟩ := hu.bounded_above_of_compact_support hus
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
  set S : Set (H E n 0) := {x | |ldet x| ≤ R} with hSdef
  have hSm : MeasurableSet S :=
    (isClosed_le (continuous_abs.comp (continuous_ldet (E := E) (n := n))) continuous_const).measurableSet
  have hS : D.ν S < ⊤ := CP.cp_vol hn D R
  set f : H E n 0 → ℂ := fun x => ψ.1 x.1 * u (ldet x) with hf
  have hfS : ∀ x, x ∉ S → f x = 0 := fun x hx => by
    simp only [hf]
    by_contra h
    exact hx (hR _ (right_ne_zero_of_mul h))
  have hfind : S.indicator f = f := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hfS x hx]
  have hfc : Continuous f :=
    ((continuous_of_mem π hψ).comp continuous_fst).mul (hu.comp (continuous_ldet (E := E) (n := n)))
  have hwt : ∀ x : H E n 0, 0 ≤ wt x := fun x => by
    have h1 := redSize_nonneg x.1
    have h2 := redSize_nonneg x.2
    simp only [wt]; linarith
  refine ⟨?_, fun M => ?_⟩
  · obtain ⟨C, hC⟩ := cp_decay_wt ψ hψc hA R 0
    haveI : IsFiniteMeasure (D.ν.restrict S) := isFiniteMeasure_restrict.2 hS.ne
    rw [← hfind, memLp_indicator_iff_restrict hSm]
    refine MemLp.of_bound hfc.aestronglyMeasurable (C * U) ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_))
    have h1 := hC x hx
    rw [pow_zero, mul_one] at h1
    simp only [hf, norm_mul]
    exact mul_le_mul h1 (hU _) (norm_nonneg _) ((norm_nonneg _).trans h1)
  · obtain ⟨C, hC⟩ := cp_decay_wt ψ hψc hA R M
    have hC0 : ∀ x ∈ S, 0 ≤ C := fun x hx => (mul_nonneg (norm_nonneg _) (pow_nonneg (hwt x) _)).trans (hC x hx)
    set K : ℝ≥0∞ := ENNReal.ofReal ((C * U) ^ 2) with hK
    have hpt : ∀ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖f x‖ₑ ^ 2 ≤ S.indicator (fun _ => K) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (pow_nonneg (hwt x) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : wt x ^ (2 * M) * ‖f x‖ ^ 2 = (‖ψ.1 x.1‖ * wt x ^ M * ‖u (ldet x)‖) ^ 2 := by
          simp only [hf, norm_mul]; rw [pow_mul]; ring
        rw [e]
        refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (hwt x) _)) (norm_nonneg _)) ?_ 2
        exact mul_le_mul (hC x hx) (hU _) (norm_nonneg _) (hC0 x hx)
      · rw [Set.indicator_of_notMem hx, hfS x hx]
        simp
    calc ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖ψ.1 x.1 * u (ldet x)‖ₑ ^ 2 ∂D.ν
        ≤ ∫⁻ x, S.indicator (fun _ => K) x ∂D.ν := lintegral_mono hpt
      _ = K * D.ν S := lintegral_indicator_const hSm K
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS

end DiscreteGroups.T1.G.Dcy

end
