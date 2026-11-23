import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

noncomputable section

open MeasureTheory Set

namespace PositivityTheory.KB.StokesSlices

lemma sum_insertNth' {m : ℕ} (i : Fin (m + 1)) (x : ℝ) (s : Fin m → ℝ) :
    ∑ j, i.insertNth x s j = x + ∑ j, s j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

lemma mem_Δ_insertNth {m : ℕ} (i : Fin (m + 1)) (x : ℝ) (s : Fin m → ℝ) :
    i.insertNth x s ∈ Δ (m + 1) ↔ s ∈ Δ m ∧ x ∈ Icc 0 (1 - ∑ j, s j) := by
  simp only [Δ, mem_ofPred_eq, mem_Icc, sum_insertNth', i.forall_iff_succAbove,
    Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  constructor
  · rintro ⟨⟨hx, hs⟩, h⟩
    exact ⟨⟨hs, by
      have : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs j
      linarith⟩, hx, by linarith⟩
  · rintro ⟨⟨hs, _⟩, hx, h⟩
    exact ⟨⟨hx, hs⟩, by linarith⟩

lemma isClosed_Δ (m : ℕ) : IsClosed (Δ m) := by
  have h1 : IsClosed {t : Fin m → ℝ | ∀ j, 0 ≤ t j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have h2 : IsClosed {t : Fin m → ℝ | ∑ j, t j ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
  exact h1.inter h2

lemma isCompact_Δ (m : ℕ) : IsCompact (Δ m) := by
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : Fin m → ℝ) 1)).of_isClosed_subset (isClosed_Δ m) ?_
  rintro t ⟨h0, h1⟩
  refine ⟨fun j => h0 j, fun j => ?_⟩
  calc t j ≤ ∑ k, t k := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)
    _ ≤ 1 := h1

lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := (isClosed_Δ m).measurableSet

lemma integrableOn_Δ_insertNth {m : ℕ} (i : Fin (m + 1)) (G : (Fin (m + 1) → ℝ) → ℝ)
    (W : Set (Fin (m + 1) → ℝ)) (hΔW : Δ (m + 1) ⊆ W) (hG : ContinuousOn G W)
    (c : (Fin m → ℝ) → ℝ) (hc : Continuous c) (hc0 : ∀ s ∈ Δ m, 0 ≤ c s)
    (hc1 : ∀ s ∈ Δ m, c s ≤ 1 - ∑ j, s j) :
    IntegrableOn (fun s => G (i.insertNth (c s) s)) (Δ m) := by
  refine ContinuousOn.integrableOn_compact (isCompact_Δ m) ?_
  have hcont : Continuous (fun s : Fin m → ℝ => (i.insertNth (c s) s : Fin (m + 1) → ℝ)) :=
    Continuous.finInsertNth i hc continuous_id
  refine hG.comp hcont.continuousOn ?_
  intro s hs
  exact hΔW ((mem_Δ_insertNth i _ _).2 ⟨hs, hc0 s hs, hc1 s hs⟩)

theorem subSlice : SubSlice := by
  intro m i G D W hW hΔW hG hD hderiv
  set e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm with he_def
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _
  have he : ∀ p : ℝ × (Fin m → ℝ), e p = i.insertNth p.1 p.2 := fun p => rfl
  have hDint : IntegrableOn D (Δ (m + 1)) :=
    (hD.mono hΔW).integrableOn_compact (isCompact_Δ _)
  have hS : MeasurableSet (e ⁻¹' Δ (m + 1)) := e.measurable (measurableSet_Δ _)
  have hFint : IntegrableOn (fun p => D (e p)) (e ⁻¹' Δ (m + 1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hDint
  rw [← hem.map_eq, setIntegral_map_equiv, Measure.volume_eq_prod,
    ← integral_indicator hS, integral_prod_symm _ ((integrable_indicator_iff hS).2 hFint)]
  have hA := integrableOn_Δ_insertNth i G W hΔW hG (fun s => 1 - ∑ j, s j)
    (continuous_const.sub (continuous_finset_sum _ fun j _ => continuous_apply j))
    (fun s hs => by have := hs.2; linarith) (fun s hs => le_rfl)
  have hB := integrableOn_Δ_insertNth i G W hΔW hG (fun _ => 0) continuous_const
    (fun s hs => le_rfl) (fun s hs => by have := hs.2; linarith)
  rw [← integral_sub hA hB, ← integral_indicator (measurableSet_Δ m)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Δ m
  · rw [Set.indicator_of_mem hs]
    have ha : 0 ≤ 1 - ∑ j, s j := by have := hs.2; linarith
    have h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) =
        (Icc 0 (1 - ∑ j, s j)).indicator (fun x => D (i.insertNth x s)) x := by
      intro x
      by_cases hx : x ∈ Icc 0 (1 - ∑ j, s j)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
        · rw [he]
        · show e (x, s) ∈ Δ (m + 1)
          rw [he]
          exact (mem_Δ_insertNth i x s).2 ⟨hs, hx⟩
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        show e (x, s) ∉ Δ (m + 1)
        rw [he]
        exact fun h => hx ((mem_Δ_insertNth i x s).1 h).2
    simp_rw [h1]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ha]
    have hcs : Continuous fun x : ℝ => Fin.insertNth (α := fun _ => ℝ) i x s := by
      fun_prop
    have hin : ∀ x ∈ Icc 0 (1 - ∑ j, s j), i.insertNth x s ∈ W :=
      fun x hx => hΔW ((mem_Δ_insertNth i x s).2 ⟨hs, hx⟩)
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => G (i.insertNth x s))
    · intro x hx
      rw [Set.uIcc_of_le ha] at hx
      have := hderiv _ (hin x hx)
      simpa [Fin.update_insertNth, Fin.insertNth_apply_same] using this
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ha]
      exact hD.comp hcs.continuousOn hin
  · rw [Set.indicator_of_notMem hs]
    have h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) = 0 := by
      intro x
      apply Set.indicator_of_notMem
      show e (x, s) ∉ Δ (m + 1)
      rw [he]
      exact fun h => hs ((mem_Δ_insertNth i x s).1 h).1
    simp_rw [h1]
    simp

end PositivityTheory.KB.StokesSlices
