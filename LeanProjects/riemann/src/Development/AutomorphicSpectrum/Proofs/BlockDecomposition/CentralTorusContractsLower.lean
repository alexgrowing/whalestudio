import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCentralContract

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem lowC_central_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro k _ _ _ _ n s d e U hU
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k), Units.val ⁻¹' V ⊆ U := by
    rw [(isEmbedding_val_GL (k := k) n).nhds_eq_comap] at hU
    simpa using Filter.mem_comap.mp hU
  obtain ⟨W, hW, hWV⟩ := exists_entry_nhds hV
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).mp hW
  obtain ⟨c, hc0, hcγ, hc1⟩ : ∃ c : k, c ≠ 0 ∧ ValuativeRel.valuation k c < γ ∧
      ValuativeRel.valuation k c ≤ 1 := by
    obtain ⟨x, hx0, hx1⟩ := (Valuation.IsNontrivial.exists_lt_one : ∃ x : k, x ≠ 0 ∧ ValuativeRel.valuation k x < 1)
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := k) (γ : ValuativeRel.ValueGroupWithZero k)
    have hy0 : (0 : ValuativeRel.ValueGroupWithZero k) < ValuativeRel.valuation k y := by
      rw [hy]; exact Units.zero_lt γ
    rcases le_or_gt (ValuativeRel.valuation k y) 1 with hy1 | hy1
    · refine ⟨y * x, ?_, ?_, ?_⟩
      · exact mul_ne_zero (by rintro rfl; simp at hy0) hx0
      · rw [map_mul, ← hy]; exact mul_lt_of_lt_one_right hy0 hx1
      · rw [map_mul]; first | exact mul_le_one' hy1 hx1.le | exact mul_le_one₀ hy1 zero_le' hx1.le
    · refine ⟨x, hx0, ?_, hx1.le⟩
      rw [← hy]; exact hx1.trans hy1
  refine ⟨blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1), blockScalar_central hc0 _, ?_⟩
  intro g hg
  simp only [lowC, Set.mem_ofPred_eq] at hg
  obtain ⟨hK, hlow⟩ := hg
  have hgint : ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hK
    intro i j
    exact (h i j).2
  have h0W : (0 : k) ∈ W := mem_of_mem_nhds hW
  rw [leviEmb_blockScalar]
  refine hVU (hWV _ fun i j => ?_)
  have hentry : (((GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1))⁻¹ * g *
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e i))⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j *
          c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e j) := by
    simp [GlobalTheory.DepthZeroJac.dia, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Matrix.sub_apply, hentry]
  by_cases hij : blk e j < blk e i
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [Matrix.one_apply_ne hne, sub_zero]
    apply hγ
    exact ((valuation_conj_le hc0 hc1 (hgint i j) (GlobalTheory.CompanionTheory.MoyPrasad.expo_gap 1 hij)).trans_eq
      (pow_one _)).trans_lt hcγ
  · have h0 := hlow i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [h0]
    by_cases hij' : i = j
    · subst hij'
      simpa [hc0] using h0W
    · simpa [Matrix.one_apply_ne hij'] using h0W

end GlobalTheory.CompanionTheory.MoyPrasad

end
