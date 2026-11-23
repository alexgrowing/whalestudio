import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBound

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem exists_layer_of_mem_genSub (hE : IsGlRep E) (hVk : IsKStableSub ε E V) {w : M}
    (hw : w ∈ genSub E V) : ∃ m, w ∈ layer ε E V m := by
  rw [genSub_eq_iSup_layer (ε := ε) hE hVk] at hw
  exact (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun _ _ h => layer_mono h)).1 hw

theorem k_highest_weight_layer_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ m, ∃ ws : Fin m → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin m, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧ (ws j ≠ 0 →
        IsNCSum ε ((j : ℕ) + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
        casValK ε (lowK ε lam) + 2 * (((j : ℕ) : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ) := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hV.2.1 hw
  obtain ⟨w₀, hw₀, hμ₀, ws, hsum, hws⟩ := layer_khw_decomp hE hU hV.1 hV.2.1 hm hμ
  refine ⟨w₀, hw₀, hμ₀, m, ws, hsum, fun j => ⟨(hws j).1, fun hj0 => ?_⟩⟩
  obtain ⟨hnc, hcas⟩ := khw_layer_succ_bound hE hU hV hc hmono hh hbig (j : ℕ) (hws j).1
    (hws j).2.1 hj0 (hws j).2.2
  obtain ⟨a, b, hab⟩ := isNCSum_succ_exists hnc
  have := (gap_gt hab hbig).2
  exact ⟨hnc, by linarith, hcas⟩

theorem casimir_gap_at_noncompact_weight (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) (hne : μ ≠ lowK ε lam) :
    ∃ j : ℕ, IsNCSum ε (j + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
      casValK ε (lowK ε lam) + 2 * ((j : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w₀, hw₀, -, m, ws, hsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  by_cases hex : ∃ j, ws j ≠ 0
  · obtain ⟨j, hj⟩ := hex
    exact ⟨j, (hws j).2 hj⟩
  · simp only [not_exists, not_not] at hex
    exfalso
    have hww : w = w₀ := by simp [hsum, hex]
    have hw0' : w₀ ≠ 0 := hww ▸ hw0
    have hμ' : IsKHWVec ε E μ w₀ := hww ▸ hμ
    obtain ⟨j, hj, hnc⟩ := khw_layer_weight hE hU hV 0 (show w₀ ∈ layer ε E V 0 from hw₀) hw0' hμ'
    have hj0 : j = 0 := by omega
    subst hj0
    exact hne (sub_eq_zero.1 (isNCSum_zero.1 hnc))

theorem khw_lowK_mem (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {w : M} (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E (lowK ε lam) w) :
    w ∈ V := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨w₀, hw₀, -, m, ws, hsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  have hz : ∀ j, ws j = 0 := by
    intro j
    by_contra hj
    obtain ⟨-, hpos, hcas⟩ := (hws j).2 hj
    have : (0 : ℝ) < 2 * (((j : ℕ) : ℝ) + 1) * (h - n + 1) := mul_pos (by positivity) hpos
    linarith
  rw [hsum]
  simp [hz, hw₀]

theorem casValK_lowK_lt (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {μ : Fin n → ℝ} {w : M} (hw : w ∈ genSub E V) (hw0 : w ≠ 0)
    (hμ : IsKHWVec ε E μ w) (hne : μ ≠ lowK ε lam) :
    casValK ε (lowK ε lam) < casValK ε μ := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨j, -, hpos, hcas⟩ := casimir_gap_at_noncompact_weight hE hU hV hc hmono hh hbig hw hw0 hμ hne
  have : (0 : ℝ) < 2 * ((j : ℝ) + 1) * (h - n + 1) := mul_pos (by positivity) hpos
  linarith

theorem vogan_min (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {μ : Fin n → ℝ} {w : M} (hw : w ∈ genSub E V) (hw0 : w ≠ 0)
    (hμ : IsKHWVec ε E μ w) :
    nsq (lowK ε lam + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε) := by
  by_cases hne : μ = lowK ε lam
  · rw [hne]
  · obtain ⟨hmono, h, hh, hbig⟩ := hgap
    obtain ⟨j, hnc, -, hcas⟩ := casimir_gap_at_noncompact_weight hE hU hV hc hmono hh hbig hw hw0 hμ hne
    have e : lowK ε lam + (μ - lowK ε lam) = μ := by abel
    have hv := vogan_num (Λ := lowK ε lam) (ν := μ - lowK ε lam) (j := j + 1) (by omega) hnc hbig
      (by rw [e]; push_cast; exact hcas)
    rwa [e] at hv

theorem khw_mem_layer (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (μ : Fin n → ℝ) :
    ∃ k : ℕ, ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ layer ε E V k := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  refine ⟨⌈(casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1))⌉₊, fun w hw hμ => ?_⟩
  obtain ⟨w₀, hw₀, -, m, ws, hsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  rw [hsum]
  refine Submodule.add_mem _ (layer_mono (Nat.zero_le _) hw₀) (Submodule.sum_mem _ fun j _ => ?_)
  by_cases hj : ws j = 0
  · rw [hj]
    exact Submodule.zero_mem _
  · obtain ⟨-, hpos, hcas⟩ := (hws j).2 hj
    refine layer_mono ?_ (hws j).1
    have hle : ((j : ℕ) : ℝ) + 1 ≤
        (casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1)) := by
      rw [le_div_iff₀ (mul_pos two_pos hpos)]
      nlinarith
    have := hle.trans (Nat.le_ceil _)
    exact_mod_cast this

theorem admissible (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (μ : Fin n → ℝ) :
    ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ S ≤ genSub E V ∧ IsKStableSub ε E S ∧
      ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ S := by
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  exact ⟨layer ε E V k, finiteDimensional_layer hV.1 k, layer_le_genSub k,
    layer_kStable hE hV.2.1 k, hk⟩

theorem re_inner_casimirK_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k) :
    RCLike.re (inner ℂ (casimirK ε E x) x) ≤
      ((√(nsq (lowK ε lam + rhoC ε)) + √2 * k) ^ 2 - nsq (rhoC ε)) * ‖x‖ ^ 2 := by
  refine re_inner_casimirK_le hE (isKUnitary_of_isInfUnitary hU) (finiteDimensional_layer hV.1 k)
    (layer_kStable hE hV.2.1 k) _ ?_ x hx
  intro w hw hw0 μ hμ
  obtain ⟨j, hj, hnc⟩ := khw_layer_weight hE hU hV k hw hw0 hμ
  have := degree_num (Λ := lowK ε lam) hj hnc
  rwa [show lowK ε lam + (μ - lowK ε lam) = μ by abel] at this

end Unitary

end ReciprocityTheory.ChartRestriction.DS
