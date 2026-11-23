import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CovolumeCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module ZSpan

noncomputable section

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}

theorem LatticeCount.exists_near (B : ShortLatticeBasis La c) (x : V) :
    ∃ μ ∈ La, ‖x + μ‖ ≤ finrank ℝ V * c := by
  let e := basisOfLinearIndependentOfCardEqFinrank' B.vec B.linearIndependent (Fintype.card_fin _)
  have he : ∀ i, e i = B.vec i := fun i ↦ by simp [e]
  refine ⟨-((floor e x : Submodule.span ℤ (Set.range e)) : V), ?_, ?_⟩
  · refine La.neg_mem ?_
    have hle : Submodule.span ℤ (Set.range e) ≤ La := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact B.mem i
    exact hle (floor e x).2
  · rw [← sub_eq_add_neg, ← fract_apply]
    calc ‖fract e x‖ ≤ ∑ i, ‖e i‖ := norm_fract_le e x
      _ ≤ ∑ _i : Fin (finrank ℝ V), c :=
          Finset.sum_le_sum fun i _ ↦ by rw [he]; exact B.norm_le i
      _ = _ := by simp

theorem LatticeCount.encard_le (B : ShortLatticeBasis La c) (b : ℝ) (x : V) :
    {y : V | y ∈ La ∧ ‖y‖ ≤ b}.encard ≤
      {g : La | g +ᵥ x ∈ closedBall (0 : V) (b + finrank ℝ V * c)}.encard := by
  classical
  obtain ⟨μ, hμ, hxμ⟩ := LatticeCount.exists_near La B x
  refine Set.encard_le_encard_of_injOn
    (f := fun y : V ↦ if h : y ∈ La then (⟨y + μ, La.add_mem h hμ⟩ : La) else 0) ?_ ?_
  · rintro y ⟨hy, hyb⟩
    simp only [Set.mem_ofPred_eq, hy, dif_pos, mem_closedBall, dist_zero_right,
      Submodule.vadd_def, vadd_eq_add]
    calc ‖y + μ + x‖ = ‖y + (x + μ)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖x + μ‖ := norm_add_le _ _
      _ ≤ b + finrank ℝ V * c := add_le_add hyb hxμ
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ h
    simp only [hy, hy', dif_pos, Subtype.mk.injEq, add_left_inj] at h
    exact h

end

theorem LatticeCount.proof : LatticeCount.Statement := by
  intro V _ _ _ _ _ La _ _ c b B hb
  set R := finrank ℝ V with hRdef
  set S := {x : V | x ∈ La ∧ ‖x‖ ≤ b}
  have hfin : S.Finite := finite_lattice_closedBall La b
  refine ⟨hfin, ?_⟩
  have hRc : 0 ≤ (R : ℝ) * c := by
    rcases Nat.eq_zero_or_pos R with h | h
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (B.norm_le ⟨0, h⟩))
  set r := b + R * c with hrdef
  have hr : 0 ≤ r := add_nonneg hb hRc
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  set bz := Free.chooseBasis ℤ La
  have hF := ZLattice.isAddFundamentalDomain bz volume
  set F := fundamentalDomain (bz.ofZLatticeBasis ℝ La)
  set A := closedBall (0 : V) r
  have hA : MeasurableSet A := measurableSet_closedBall
  have hmeas : ∀ g : La, Measurable fun x : V ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x) :=
    fun g ↦ (measurable_one.indicator hA).comp (measurable_const_vadd g)
  have key : ∀ x : V,
      (S.encard : ENNReal) ≤ ∑' g : La, A.indicator (1 : V → ENNReal) (g +ᵥ x) := by
    intro x
    have hind : (fun g : La ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x)) =
        {g : La | g +ᵥ x ∈ A}.indicator 1 := by
      funext g
      by_cases hg : g +ᵥ x ∈ A <;> simp [hg]
    rw [hind, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    exact_mod_cast LatticeCount.encard_le La B b x
  have hFfin : volume F ≠ ⊤ := (fundamentalDomain_isBounded _).measure_lt_top.ne
  have hvol : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) ≤ volume A := by
    calc (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La)
        = (S.encard : ENNReal) * volume F := by
          rw [ZLattice.covolume_eq_measure_fundamentalDomain La volume hF,
            ofReal_measureReal hFfin]
      _ = ∫⁻ _ in F, (S.encard : ENNReal) := (setLIntegral_const F _).symm
      _ ≤ ∫⁻ x in F, ∑' g : La, A.indicator 1 (g +ᵥ x) := lintegral_mono key
      _ = ∑' g : La, ∫⁻ x in F, A.indicator 1 (g +ᵥ x) :=
          lintegral_tsum fun g ↦ (hmeas g).aemeasurable
      _ = ∫⁻ x, A.indicator 1 x := (hF.lintegral_eq_tsum'' _).symm
      _ = volume A := lintegral_indicator_one hA
  have hunit : volume (ball (0 : V) 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) := by
    let f := (stdOrthonormalBasis ℝ V).repr
    rw [← f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet,
      f.preimage_ball, map_zero]
  have hunitfin : volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) ≠ ⊤ :=
    isBounded_ball.measure_lt_top.ne
  have hball : volume A = ENNReal.ofReal (unitBallVolume R * r ^ R) := by
    rw [Measure.addHaar_closedBall volume 0 hr, hunit, unitBallVolume,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hunitfin, mul_comm]
  have hS : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) =
      ENNReal.ofReal (S.ncard * ZLattice.covolume La) := by
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hpos : 0 ≤ unitBallVolume R * r ^ R :=
    mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr _)
  have := (hS ▸ hvol).trans_eq hball
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
