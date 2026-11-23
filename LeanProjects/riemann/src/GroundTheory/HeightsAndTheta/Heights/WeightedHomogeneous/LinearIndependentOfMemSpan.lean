import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

namespace HadamardGramBound

theorem linearIndependent_of_mem_span {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℕ} (v b : Fin r → E) (hv : LinearIndependent ℝ v)
    (hb : ∀ i, v i ∈ Submodule.span ℤ (Set.range b)) : LinearIndependent ℝ b := by
  have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℝ (Set.range b) (hb i)
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = r := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have h2 : r ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := by
    have := Submodule.finrank_mono hle
    omega
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) ≤ r := by
    simpa [Set.finrank] using finrank_range_le_card (R := ℝ) b
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank]
  omega

theorem equiv : GroundTheory.Heights₂.Heights.HadamardGramBound.Statement ↔
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound.Statement := by
  constructor
  · intro hA E _ _ r v hv hn
    have key : ∀ b : Fin r → E, (∀ i, v i ∈ Submodule.span ℤ (Set.range b)) →
        0 ≤ -Real.log (Real.sqrt (gram b)) := by
      intro b hb
      obtain ⟨_, h1⟩ := hA E r v b hv hn hb
      rw [neg_nonneg]
      have h1' : gram b ≤ 1 := h1
      refine Real.log_nonpos (Real.sqrt_nonneg _) ?_
      simpa using Real.sqrt_le_sqrt h1'
    refine ⟨key v fun i ↦ Submodule.subset_span ⟨i, rfl⟩, fun b _ hb ↦ key b fun i ↦ ?_⟩
    have h := hb i
    rwa [← Submodule.span_int_eq_addSubgroupClosure] at h
  · intro hB V _ _ r v b hv hn hb
    have hbli := linearIndependent_of_mem_span v b hv hb
    have hpos : 0 < gram b := (Matrix.posDef_gram_of_linearIndependent hbli).det_pos
    have h := (hB V r v hv hn).2 b hbli fun i ↦ by
      rw [← Submodule.span_int_eq_addSubgroupClosure]
      exact hb i
    rw [neg_nonneg, Real.log_nonpos_iff (Real.sqrt_nonneg _),
      Real.sqrt_le_left zero_le_one, one_pow] at h
    exact ⟨hpos, h⟩

end HadamardGramBound

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
