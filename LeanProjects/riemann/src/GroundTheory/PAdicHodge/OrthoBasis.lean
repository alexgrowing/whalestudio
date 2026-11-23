import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]

omit [IsUltrametricDist k] [IsUltrametricDist E] in

theorem exists_sub_far_of_isClosed {U : Submodule k E} (hU : IsClosed (U : Set E)) {x : E}
    (hx : x ∉ U) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ u ∈ U, ∀ u' ∈ U, s * ‖x - u‖ ≤ ‖x - u - u'‖ := by
  have hne : (U : Set E).Nonempty := ⟨0, U.zero_mem⟩
  have hd : 0 < Metric.infDist x U := (hU.notMem_iff_infDist_pos hne).1 hx
  have hlt : Metric.infDist x U < Metric.infDist x U / s := by
    rw [lt_div_iff₀ hs0]; nlinarith
  obtain ⟨u, huU, hu⟩ := (Metric.infDist_lt_iff hne).1 hlt
  refine ⟨u, huU, fun u' hu' => ?_⟩
  have h1 : Metric.infDist x U ≤ dist x (u + u') :=
    Metric.infDist_le_dist_of_mem (U.add_mem huU hu')
  rw [dist_eq_norm, ← sub_sub] at h1
  rw [dist_eq_norm] at hu
  have h2 := (lt_div_iff₀ hs0).1 hu
  nlinarith

omit [IsUltrametricDist k] in

theorem le_norm_smul_add_of_far {U : Submodule k E} {w : E} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hw : ∀ u' ∈ U, s * ‖w‖ ≤ ‖w - u'‖) (a : k) {u : E} (hu : u ∈ U) :
    s * ‖a • w‖ ≤ ‖a • w + u‖ ∧ s * ‖u‖ ≤ ‖a • w + u‖ := by
  have h1 : s * ‖a • w‖ ≤ ‖a • w + u‖ := by
    by_cases ha : a = 0
    · simp [ha]
    · have he : a • w + u = a • (w - (-a⁻¹ • u)) := by
        rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ ha, neg_one_smul, sub_neg_eq_add]
      rw [he, norm_smul, norm_smul]
      have := hw (-a⁻¹ • u) (U.smul_mem _ hu)
      nlinarith [norm_nonneg a]
  refine ⟨h1, ?_⟩
  have h2 : ‖u‖ ≤ max ‖a • w + u‖ ‖a • w‖ := by
    have := IsUltrametricDist.norm_add_le_max (a • w + u) (-(a • w))
    have e : a • w + u + -(a • w) = u := by abel
    rwa [e, norm_neg] at this
  rcases le_max_iff.1 h2 with h | h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]

variable [CompleteSpace k]

theorem exists_orthogonal_fin (n : ℕ) : ∀ (v : Fin n → E), LinearIndependent k v →
    ∀ {τ : ℝ}, 0 < τ → τ < 1 →
    ∃ w : Fin n → E, (∀ i, w i ≠ 0) ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : Fin n → k) (i : Fin n), τ * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  induction n with
  | zero =>
    intro v _ τ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ i => i.elim0⟩
  | succ n ih =>
    intro v hv τ hτ0 hτ1
    set s := Real.sqrt τ with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hτ0
    have hs1 : s < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt hτ0.le hτ1
    have hss : s * s = τ := Real.mul_self_sqrt hτ0.le
    obtain ⟨w', hw'0, hw'mem, hw'⟩ :=
      ih (fun i => v i.castSucc) (hv.comp _ (Fin.castSucc_injective n)) hs0 hs1
    set U := Submodule.span k (Set.range w') with hUdef
    have : FiniteDimensional k U := FiniteDimensional.span_of_finite k (Set.finite_range w')
    have hUc : IsClosed (U : Set E) := U.closed_of_finiteDimensional
    have hrange : (Set.range fun i : Fin n => v i.castSucc) = v '' Set.range Fin.castSucc :=
      Set.range_comp v Fin.castSucc
    have hUv : U ≤ Submodule.span k (Set.range fun i : Fin n => v i.castSucc) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hw'mem)
    have hvv : Submodule.span k (Set.range fun i : Fin n => v i.castSucc) ≤
        Submodule.span k (Set.range v) :=
      Submodule.span_mono (Set.range_comp_subset_range _ _)
    have hx : v (Fin.last n) ∉ U := by
      intro h
      have h' := hUv h
      rw [hrange] at h'
      exact hv.notMem_span_image (s := Set.range Fin.castSucc) (x := Fin.last n)
        (by rintro ⟨j, hj⟩; exact (Fin.castSucc_lt_last j).ne hj) h'
    obtain ⟨u, huU, hu⟩ := exists_sub_far_of_isClosed hUc hx hs0 hs1
    set x := v (Fin.last n) - u with hxdef
    have hx0 : x ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero] at h
      rw [h]; exact huU
    have hfar : ∀ u' ∈ U, s * ‖x‖ ≤ ‖x - u'‖ := hu
    refine ⟨(Fin.snoc w' x : Fin (n + 1) → E), ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hx0
      | cast i => simpa using hw'0 i
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨Fin.last n, rfl⟩) (hvv (hUv huU))
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact hvv (hw'mem i)
    · intro c i
      have hsum : ∑ j, c j • (Fin.snoc w' x : Fin (n + 1) → E) j =
          c (Fin.last n) • x + ∑ j : Fin n, c j.castSucc • w' j := by
        rw [Fin.sum_univ_castSucc, add_comm]
        simp
      have hu'U : ∑ j : Fin n, c j.castSucc • w' j ∈ U :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨h1, h2⟩ := le_norm_smul_add_of_far hs0 hs1.le hfar (c (Fin.last n)) hu'U
      rw [hsum]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        have : τ * ‖c (Fin.last n) • x‖ ≤ s * ‖c (Fin.last n) • x‖ := by
          rw [← hss]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
        linarith
      | cast i =>
        simp only [Fin.snoc_castSucc]
        have h3 := hw' (fun j => c j.castSucc) i
        rw [← hss, mul_assoc]
        nlinarith

theorem exists_orthogonal_of_linearIndependent {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : LinearIndependent k v) {t : ℝ} (ht : t < 1) :
    ∃ w : ι → E, LinearIndependent k w ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : ι → k) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  set τ := max t (1 / 2) with hτ
  have hτ0 : 0 < τ := lt_max_of_lt_right (by norm_num)
  have hτ1 : τ < 1 := max_lt ht (by norm_num)
  let e := Fintype.equivFin ι
  obtain ⟨w, hw0, hwmem, hw⟩ := exists_orthogonal_fin (Fintype.card ι) (v ∘ e.symm)
    (hv.comp _ e.symm.injective) hτ0 hτ1
  have hsum : ∀ c : ι → k, ∑ j, c j • w (e j) = ∑ j, (c ∘ e.symm) j • w j := by
    intro c
    have := e.sum_comp (fun j => (c ∘ e.symm) j • w j)
    simpa using this
  have horth : ∀ (c : ι → k) (i : ι), τ * ‖c i • w (e i)‖ ≤ ‖∑ j, c j • w (e j)‖ := by
    intro c i
    rw [hsum]
    simpa using hw (c ∘ e.symm) (e i)
  refine ⟨fun i => w (e i), ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := horth g i
    rw [hg, norm_zero] at h
    have h0 : ‖g i • w (e i)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (g i • w (e i))]) (norm_nonneg _)
    rw [norm_eq_zero, smul_eq_zero] at h0
    exact h0.resolve_right (hw0 (e i))
  · intro i
    have := hwmem (e i)
    rwa [e.symm.surjective.range_comp v] at this
  · intro c i
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans (horth c i)

end GroundTheory.PAdicHodge
