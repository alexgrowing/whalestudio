import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff Manifold

namespace GlobalTheory

theorem exists_smooth_compact_partition_on_compact :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (K : Set Z),
    IsCompact K → ∀ (ι : Type) [Fintype ι] (U : ι → Set Z), (∀ i, IsOpen (U i)) →
    K ⊆ ⋃ i, U i → ∃ φ : ι → Z → ℂ, (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧
      tsupport (φ i) ⊆ U i) ∧ ∀ z ∈ K, ∑ i, φ i z = 1 := by
  intro Z _ _ _ K hK ι _ U hU hKU
  classical
  haveI : ProperSpace Z := FiniteDimensional.proper ℝ Z
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Z)
  have hcov : K ⊆ ⋃ i, U i ∩ Metric.ball (0 : Z) R := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKU hz)
    exact Set.mem_iUnion.2 ⟨i, hi, hR hz⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ Z)
    hK.isClosed (fun i => U i ∩ Metric.ball (0 : Z) R)
    (fun i => (hU i).inter Metric.isOpen_ball) hcov
  have hρs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i =>
    contMDiff_iff_contDiff.1 (ρ i).contMDiff
  refine ⟨fun i z => ((ρ i z : ℝ) : ℂ), fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hρs i)
  · have h1 : tsupport (fun z => ((ρ i z : ℝ) : ℂ)) ⊆ tsupport (ρ i) :=
      tsupport_comp_subset Complex.ofReal_zero _
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Z) R) (isClosed_tsupport _) ?_
    exact h1.trans ((hρ i).trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
  · exact (tsupport_comp_subset Complex.ofReal_zero _).trans ((hρ i).trans Set.inter_subset_left)
  · intro z hz
    have h2 := ρ.sum_eq_one hz
    rw [finsum_eq_sum_of_fintype] at h2
    simp only
    rw [← Complex.ofReal_sum, h2, Complex.ofReal_one]

end GlobalTheory
