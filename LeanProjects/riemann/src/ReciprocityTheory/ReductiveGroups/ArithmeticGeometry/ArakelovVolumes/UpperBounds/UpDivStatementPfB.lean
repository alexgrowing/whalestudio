import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivB

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  calc ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖x i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

def stp {p : ℕ} (α : Fin p → ℕ) (k : Fin p) : Fin p → ℕ := fun i => α i + if i = k then 1 else 0

theorem mem_step {p N : ℕ} {α : Fin p → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple p N) (k : Fin p) :
    stp α k ∈ Finset.Nat.antidiagonalTuple p (N + 1) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at hα ⊢
  simp [stp, Finset.sum_add_distrib, hα]

theorem pow_step {p : ℕ} (g : Fin p → ℂ) (α : Fin p → ℕ) (k : Fin p) :
    ∏ i, g i ^ stp α k i = (∏ i, g i ^ α i) * g k := by
  simp only [stp, pow_add, Finset.prod_mul_distrib]
  congr 1
  have h : ∀ i, g i ^ (if i = k then 1 else 0) = if i = k then g i else 1 := by
    intro i; split_ifs <;> simp
  simp only [h, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem iter_div (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (τ0 : ℝ) : ∀ (N : ℕ), (p : ℝ) - 1 < τ0 - N - 1 + 1 →
    ∀ F : V n → ℂ, DifferentiableOn ℂ F U →
    ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-τ0) * Real.exp (-ph0 y)) < ⊤ →
    ∃ H : (Fin p → ℕ) → V n → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple p N, DifferentiableOn ℂ (H α) U ∧
        ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - N)) *
          Real.exp (-ph0 y)) < ⊤) ∧
      ∀ y ∈ U, F y = ∑ α ∈ Finset.Nat.antidiagonalTuple p N, (∏ i, g i y ^ α i) * H α y := by
  have hSpos : ∀ y ∈ U, 0 < ∑ i, ‖g i y‖ ^ 2 := by
    intro y hy
    obtain ⟨i, hi⟩ := hnz y hy
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hScont : ContinuousOn (fun y => ∑ i, ‖g i y‖ ^ 2) U :=
    continuousOn_finsetSum _ fun i _ => ((hg i).continuousOn.norm).pow 2
  intro N
  induction N with
  | zero =>
    intro _ F hF hI
    refine ⟨fun _ => F, fun α hα => ⟨hF, by simpa using hI⟩, fun y _ => ?_⟩
    rw [Finset.Nat.antidiagonalTuple_zero_right]
    simp
  | succ N ih =>
    intro hN F hF hI
    have hN' : (p : ℝ) - 1 < τ0 - N - 1 + 1 := by push_cast at hN; linarith
    obtain ⟨H, hH, hid⟩ := ih hN' F hF hI
    set t : ℝ := τ0 - N - 1 with htdef
    have ht : (p : ℝ) - 1 < t := by rw [htdef]; push_cast at hN; linarith
    have hstep : ∀ α ∈ Finset.Nat.antidiagonalTuple p N, ∃ hh : Fin p → V n → ℂ,
        (∀ i, DifferentiableOn ℂ (hh i) U) ∧ (∀ y ∈ U, H α y = ∑ i, g i y * hh i y) ∧
        ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 y)) < ⊤ := by
      intro α hα
      have hIα : ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) *
          Real.exp (-ph0 y)) < ⊤ := by
        have e : -(t + 1) = -(τ0 - N) := by rw [htdef]; ring
        rw [e]; exact (hH α hα).2
      obtain ⟨hh, hhd, hhid, hhest⟩ := UpDivA.skoda_open hU S hz g ph0 t (H α) hp hg hnz hph hl ht
        (hH α hα).1 hIα
      exact ⟨hh, hhd, hhid, lt_of_le_of_lt hhest (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIα)⟩
    choose! hh hhd hhid hhI using hstep
    set A := Finset.Nat.antidiagonalTuple p N with hA
    obtain ⟨w, hw⟩ : ∃ w : V n → ℝ, w = fun y => (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y) :=
      ⟨_, rfl⟩
    have hw0 : ∀ y, 0 ≤ w y := fun y => by
      rw [hw]; exact mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _)
        (Real.exp_pos _).le
    have hwc : ContinuousOn w U := by
      rw [hw]
      exact (hScont.rpow_const fun y hy => Or.inl (hSpos y hy).ne').mul
        (Real.continuous_exp.comp_continuousOn hph.continuousOn.neg)
    refine ⟨fun β y => ∑ α ∈ A, ∑ k, if stp α k = β then hh α k y else 0,
      fun β _ => ⟨?_, ?_⟩, ?_⟩
    · have hk : ∀ α ∈ A, ∀ k ∈ (Finset.univ : Finset (Fin p)),
          DifferentiableOn ℂ (fun y => if stp α k = β then hh α k y else 0) U := by
        intro α hα k _
        by_cases hk : stp α k = β
        · simp only [hk, if_true]; exact hhd α hα k
        · simp only [hk, if_false]; exact differentiableOn_const (c := (0 : ℂ))
      have hα : ∀ α ∈ A, DifferentiableOn ℂ
          (fun y => ∑ k, if stp α k = β then hh α k y else 0) U := fun α hα =>
        (DifferentiableOn.sum (u := Finset.univ) (A := fun k y => if stp α k = β then hh α k y else 0)
          (hk α hα)).congr fun y _ => by simp [Finset.sum_apply]
      exact (DifferentiableOn.sum (u := A)
        (A := fun α y => ∑ k, if stp α k = β then hh α k y else 0) hα).congr fun y _ => by
          simp [Finset.sum_apply]
    · set C : ℝ := ((A ×ˢ (Finset.univ : Finset (Fin p))).card : ℝ) with hC
      have hpt : ∀ y, ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          ≤ C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2 := by
        intro y
        rw [← Finset.sum_product']
        refine (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact le_rfl
        · simp
      have hbound : ∀ y, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          * w y) ≤ ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y) := by
        intro y
        rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
          by positivity) (hw0 y)), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y
            ≤ (C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2) * w y := mul_le_mul_of_nonneg_right (hpt y) (hw0 y)
          _ = C * ∑ α ∈ A, (∑ k, ‖hh α k y‖ ^ 2) * w y := by rw [mul_assoc, Finset.sum_mul]
      have hfin : ∫⁻ y in U, ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y)
          < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [lintegral_finsetSum']
        · refine ENNReal.sum_lt_top.mpr fun α hα => ?_
          have := hhI α hα
          rw [hw]
          simpa [mul_assoc] using this
        · intro α hα
          have hc : ContinuousOn (fun y => (∑ k, ‖hh α k y‖ ^ 2) * w y) U :=
            (continuousOn_finsetSum _ fun k _ => ((hhd α hα k).continuousOn.norm).pow 2).mul hwc
          exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hU.measurableSet
      have e2 : (fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y))) =
          fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y) := by
        funext y
        rw [hw, mul_assoc]
        congr 4
        rw [htdef]; push_cast; ring
      show ∫⁻ y in U, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y)) < ⊤
      rw [e2]
      exact lt_of_le_of_lt (lintegral_mono hbound) hfin
    · intro y hy
      rw [hid y hy]
      have h1 : ∀ α ∈ A, (∏ i, g i y ^ α i) * H α y =
          ∑ k, (∏ i, g i y ^ stp α k i) * hh α k y := by
        intro α hα
        rw [hhid α hα y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_step]; ring
      rw [Finset.sum_congr rfl h1]
      symm
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (mem_step hα k)]

end UpDivB

end ReciprocityTheory.ChartRestriction.G.AR.Up
