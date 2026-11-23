import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake

noncomputable def lay (x : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' l : ℕ, if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0

theorem lay_le (x : ℝ≥0∞) : lay x ≤ x := by
  have key : ∀ N : ℕ,
      ∑ l ∈ Finset.range N, (if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) ≤ x ∧
      ∑ l ∈ Finset.range N, (if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) ≤ N := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : ((n : ℝ≥0∞) + 1) < x
      · simp only [h, if_true]
        have h1 := add_le_add_left ih.2 (1 : ℝ≥0∞)
        exact ⟨h1.trans h.le, by push_cast; exact h1⟩
      · simp only [h, if_false, add_zero]
        exact ⟨ih.1, ih.2.trans (by exact_mod_cast Nat.le_succ n)⟩
  rw [lay, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => (key N).1

theorem nat_le_lay {x : ℝ≥0∞} {N : ℕ} (h : (N : ℝ≥0∞) < x) : (N : ℝ≥0∞) ≤ lay x := by
  have h1 : ∑ l ∈ Finset.range N, (if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) = N := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro l hl
      have hl' : l + 1 ≤ N := Finset.mem_range.1 hl
      have : ((l : ℝ≥0∞) + 1) ≤ N := by exact_mod_cast hl'
      simp [this.trans_lt h]
  rw [← h1]
  exact ENNReal.sum_le_tsum _

theorem le_lay_add_one (x : ℝ≥0∞) : x ≤ lay x + 1 := by
  by_cases top : x = ∞
  · subst top
    have : lay ∞ = ∞ := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
      exact absurd (nat_le_lay (N := n) (ENNReal.natCast_lt_top n)) (not_le.2 hn)
    simp [this]
  · lift x to NNReal using top
    have hx : x ≤ (⌈x⌉₊ : NNReal) := Nat.le_ceil x
    have hx' : (x : ℝ≥0∞) ≤ (⌈x⌉₊ : ℝ≥0∞) := by exact_mod_cast hx
    rcases hm : ⌈x⌉₊ with _ | n
    · rw [hm] at hx'
      exact hx'.trans (by simp)
    · have hn : (n : NNReal) < x := Nat.lt_ceil.1 (by omega)
      have hn' : (n : ℝ≥0∞) < x := by exact_mod_cast hn
      rw [hm] at hx'
      refine hx'.trans ?_
      push_cast
      exact add_le_add_left (nat_le_lay hn') 1

theorem two_lt_two {a b : ℝ≥0∞} (h : a < b) : 2 * a < 2 * b :=
  (ENNReal.mul_lt_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).2 h

theorem two_mul_lay_le (x : ℝ≥0∞) : 2 * lay x ≤ lay (2 * x) := by
  have e : lay (2 * x) =
      (∑' l : ℕ, if (((2 * l : ℕ) : ℝ≥0∞) + 1) < 2 * x then (1 : ℝ≥0∞) else 0) +
      ∑' l : ℕ, if (((2 * l + 1 : ℕ) : ℝ≥0∞) + 1) < 2 * x then (1 : ℝ≥0∞) else 0 := by
    rw [lay]
    exact (tsum_even_add_odd ENNReal.summable ENNReal.summable).symm
  rw [two_mul, e, lay]
  refine add_le_add (ENNReal.tsum_le_tsum fun l => ?_) (ENNReal.tsum_le_tsum fun l => ?_)
  · by_cases h : ((l : ℝ≥0∞) + 1) < x
    · have h2 := two_lt_two h
      have h3 : (((2 * l : ℕ) : ℝ≥0∞) + 1) < 2 * x := by
        refine lt_of_le_of_lt ?_ h2
        push_cast
        rw [mul_add]
        gcongr
        norm_num
      rw [if_pos h, if_pos h3]
    · simp [h]
  · by_cases h : ((l : ℝ≥0∞) + 1) < x
    · have h2 := two_lt_two h
      have h3 : (((2 * l + 1 : ℕ) : ℝ≥0∞) + 1) < 2 * x := by
        refine lt_of_le_of_lt (le_of_eq ?_) h2
        push_cast
        ring
      rw [if_pos h, if_pos h3]
    · simp [h]

noncomputable def dy (k : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ := (2 ^ k : ℝ≥0∞)⁻¹ * lay (2 ^ k * x)

theorem two_pow_ne_zero' (k : ℕ) : (2 ^ k : ℝ≥0∞) ≠ 0 := by simp
theorem two_pow_ne_top' (k : ℕ) : (2 ^ k : ℝ≥0∞) ≠ ∞ := by simp

theorem dy_le_succ (k : ℕ) (x : ℝ≥0∞) : dy k x ≤ dy (k + 1) x := by
  have e : (2 ^ k : ℝ≥0∞)⁻¹ = (2 ^ (k + 1) : ℝ≥0∞)⁻¹ * 2 := by
    rw [pow_succ, ENNReal.mul_inv (Or.inl (two_pow_ne_zero' k)) (Or.inl (two_pow_ne_top' k)),
      mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  have e2 : (2 ^ (k + 1) : ℝ≥0∞) * x = 2 * (2 ^ k * x) := by rw [pow_succ]; ring
  rw [dy, dy, e, e2, mul_assoc]
  gcongr
  exact two_mul_lay_le _

theorem dy_mono (x : ℝ≥0∞) : Monotone fun k => dy k x :=
  monotone_nat_of_le_succ fun k => dy_le_succ k x

theorem inv_mul_cancel_two_pow (k : ℕ) (x : ℝ≥0∞) : (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k * x) = x := by
  rw [← mul_assoc, ENNReal.inv_mul_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k), one_mul]

theorem iSup_dy (x : ℝ≥0∞) : ⨆ k, dy k x = x := by
  refine le_antisymm (iSup_le fun k => ?_) ?_
  · calc dy k x ≤ (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k * x) := by
          rw [dy]; gcongr; exact lay_le _
      _ = x := inv_mul_cancel_two_pow k x
  · have hb : ∀ k : ℕ, x ≤ (⨆ j, dy j x) + (2 : ℝ≥0∞)⁻¹ ^ k := by
      intro k
      calc x = (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k * x) := (inv_mul_cancel_two_pow k x).symm
        _ ≤ (2 ^ k : ℝ≥0∞)⁻¹ * (lay (2 ^ k * x) + 1) := by
            gcongr; exact le_lay_add_one _
        _ = dy k x + (2 : ℝ≥0∞)⁻¹ ^ k := by rw [mul_add, mul_one, ENNReal.inv_pow, dy, ENNReal.inv_pow]
        _ ≤ _ := by gcongr; exact le_iSup (fun j => dy j x) k
    have ht : Filter.Tendsto (fun k : ℕ => (⨆ j, dy j x) + (2 : ℝ≥0∞)⁻¹ ^ k) Filter.atTop
        (nhds ((⨆ j, dy j x) + 0)) :=
      tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (ENNReal.inv_lt_one.2 (by norm_num)))
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hb

theorem lt_pow_mul_iff (k : ℕ) (b x : ℝ≥0∞) :
    b < 2 ^ k * x ↔ (2 ^ k : ℝ≥0∞)⁻¹ * b < x := by
  constructor
  · intro h
    have := (ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.2 (two_pow_ne_top' k))
      (ENNReal.inv_ne_top.2 (two_pow_ne_zero' k))).2 h
    rwa [inv_mul_cancel_two_pow] at this
  · intro h
    have := (ENNReal.mul_lt_mul_iff_right (two_pow_ne_zero' k) (two_pow_ne_top' k)).2 h
    rwa [← mul_assoc, ENNReal.mul_inv_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k),
      one_mul] at this

theorem dy_eq_tsum (k : ℕ) (x : ℝ≥0∞) :
    dy k x = ∑' l : ℕ, (2 ^ k : ℝ≥0∞)⁻¹ *
      (if (2 ^ k : ℝ≥0∞)⁻¹ * ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) := by
  rw [dy, lay, ENNReal.tsum_mul_left]
  simp only [lt_pow_mul_iff]

theorem tsum_ite_lt {Y : Type} (S : Set Y) (φ : Y → ℝ≥0∞) (s : ℝ≥0∞) :
    ∑' y : S, (if s < φ y then (1 : ℝ≥0∞) else 0) =
      (((S ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype S (fun y => if s < φ y then (1 : ℝ≥0∞) else 0),
    tsum_subtype (S ∩ {y | s < φ y}) (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun y => ?_
  by_cases h1 : y ∈ S <;> by_cases h2 : s < φ y <;> simp [Set.indicator, h1, h2]

theorem tsum_iSup_of_mono {ι : Type} (f : ℕ → ι → ℝ≥0∞) (hf : ∀ i, Monotone fun k => f k i) :
    ∑' i, ⨆ k, f k i = ⨆ k, ∑' i, f k i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  refine iSup_congr fun s => ?_
  exact ENNReal.finsetSum_iSup_of_monotone hf

theorem measurable_lintegral_tsum_of_level_counts
    {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω) (ν : Measure Y)
    (L : Ω → Set Y) (φ : Y → ℝ≥0∞) (c : ℝ≥0∞) (hφ : Measurable φ)
    (hN : ∀ s : ℝ≥0∞, Measurable fun ω => (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞))
    (hI : ∀ s : ℝ≥0∞, ∫⁻ ω, (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) ∂P = c * ν {y | s < φ y}) :
    Measurable (fun ω => ∑' y : L ω, φ y) ∧ ∫⁻ ω, ∑' y : L ω, φ y ∂P = c * ∫⁻ y, φ y ∂ν := by

  have hG : ∀ k ω, ∑' y : L ω, dy k (φ y) = ∑' l : ℕ, (2 ^ k : ℝ≥0∞)⁻¹ *
      (((L ω ∩ {y | (2 ^ k : ℝ≥0∞)⁻¹ * ((l : ℝ≥0∞) + 1) < φ y}).encard : ℕ∞) : ℝ≥0∞) := by
    intro k ω
    simp_rw [dy_eq_tsum]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => ?_
    rw [ENNReal.tsum_mul_left, tsum_ite_lt]
  have hGm : ∀ k, Measurable fun ω => ∑' y : L ω, dy k (φ y) := by
    intro k
    simp_rw [hG]
    exact Measurable.ennreal_tsum fun l => (hN _).const_mul _
  have hGi : ∀ k, ∫⁻ ω, ∑' y : L ω, dy k (φ y) ∂P = c * ∫⁻ y, dy k (φ y) ∂ν := by
    intro k
    have hlev : ∀ s : ℝ≥0∞, Measurable fun y => if s < φ y then (1 : ℝ≥0∞) else 0 := fun s =>
      Measurable.ite (measurableSet_lt measurable_const hφ) measurable_const measurable_const
    have hone : ∀ s : ℝ≥0∞, ∫⁻ y, (if s < φ y then (1 : ℝ≥0∞) else 0) ∂ν = ν {y | s < φ y} := by
      intro s
      rw [← lintegral_indicator_one (measurableSet_lt measurable_const hφ)]
      refine lintegral_congr fun y => ?_
      by_cases h : s < φ y <;> simp [Set.indicator, h]
    simp_rw [hG, dy_eq_tsum]
    rw [lintegral_tsum fun l => ((hN _).const_mul _).aemeasurable,
      lintegral_tsum fun l => ((hlev _).const_mul _).aemeasurable, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [lintegral_const_mul _ (hN _), hI, lintegral_const_mul _ (hlev _), hone, mul_left_comm]
  have hmono : ∀ ω (y : L ω), Monotone fun k => dy k (φ y) := fun _ y => dy_mono _
  have hS : (fun ω => ∑' y : L ω, φ y) = fun ω => ⨆ k, ∑' y : L ω, dy k (φ y) := by
    funext ω
    rw [← tsum_iSup_of_mono (fun k (y : L ω) => dy k (φ y)) (hmono ω)]
    exact tsum_congr fun y => (iSup_dy _).symm
  have hGmono : Monotone fun k ω => ∑' y : L ω, dy k (φ y) := by
    intro j k hjk ω
    exact ENNReal.tsum_le_tsum fun y => dy_mono _ hjk
  have hdm : ∀ k, Measurable fun y => dy k (φ y) := by
    intro k
    simp_rw [dy_eq_tsum]
    exact Measurable.ennreal_tsum fun l => (Measurable.ite
      (measurableSet_lt measurable_const hφ) measurable_const measurable_const).const_mul _
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact Measurable.iSup hGm
  · rw [hS, lintegral_iSup hGm hGmono]
    simp_rw [hGi]
    rw [← ENNReal.mul_iSup, ← lintegral_iSup hdm (fun j k hjk y => dy_mono _ hjk)]
    simp_rw [iSup_dy]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake
