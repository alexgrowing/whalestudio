import Mathlib
import Formalism.HermitianLattices.StatementMass
open MeasureTheory NumberField Finset

namespace GlobalTheory.SimplexVolume

theorem volume_l1_ball (ι : Type) [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L) :
    volume {x : ι → ℝ | ∑ i, |x i| ≤ L} =
      2 ^ Fintype.card ι * ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  have h := MeasureTheory.volume_sum_rpow_le ι (p := 1) le_rfl L
  simp only [Real.rpow_one, div_one, one_add_one_eq_two, Real.Gamma_two, mul_one,
    Real.Gamma_nat_eq_factorial] at h
  rw [h, ← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_mul (by positivity)]
  have h2 : (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal (2 ^ Fintype.card ι) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem volume_pos_simplex_le (ι : Type) [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L) :
    volume {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L} ≤
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  classical
  set S : Set (ι → ℝ) := {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L} with hS
  have hSm : MeasurableSet S := by
    rw [hS]
    measurability
  let f : (ι → Bool) → ι → ℝ → ℝ := fun e i y => if e i then y else -y
  have hf : ∀ e i, MeasurePreserving (f e i) volume volume := by
    intro e i
    by_cases h : e i
    · simp only [f, h, if_true]
      exact MeasurePreserving.id (volume : Measure ℝ)
    · simpa [f, h] using Measure.measurePreserving_neg (volume : Measure ℝ)
  let R : (ι → Bool) → (ι → ℝ) → (ι → ℝ) := fun e x i => f e i (x i)
  have hR : ∀ e, MeasurePreserving (R e) volume volume := fun e =>
    volume_preserving_pi (fun i => hf e i)
  have hdisj : Pairwise (Function.onFun Disjoint fun e => R e ⁻¹' S) := by
    intro e e' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    funext i
    have h1 := hx.1 i
    have h2 := hx'.1 i
    simp only [R, f] at h1 h2
    cases he : e i <;> cases he' : e' i <;> simp [he, he'] at h1 h2 ⊢ <;> linarith
  have hsub : (⋃ e, R e ⁻¹' S) ⊆ {x : ι → ℝ | ∑ i, |x i| ≤ L} := by
    intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 hx
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) he.2
    have h1 := he.1 i
    rw [← abs_of_pos h1]
    simp only [R, f]
    split_ifs <;> simp
  have hU : volume (⋃ e, R e ⁻¹' S) = 2 ^ Fintype.card ι * volume S := by
    rw [measure_iUnion hdisj (fun e => (hR e).measurable hSm)]
    simp only [fun e => (hR e).measure_preimage hSm.nullMeasurableSet]
    simp [tsum_fintype]
  have hle := measure_mono (μ := volume) hsub
  rw [hU, volume_l1_ball ι L hL] at hle
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 hle

theorem volume_simplex_le (ι : Type) [Fintype ι] (a : ι → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    volume {t : ι → ℝ | (∀ i, a i ≤ t i) ∧ ∑ i, (t i - a i) ≤ L} ≤
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine le_trans (measure_mono (Set.subset_univ _)) ?_
    simp [volume_pi]
  · have hsub : {t : ι → ℝ | (∀ i, a i ≤ t i) ∧ ∑ i, (t i - a i) ≤ L} ⊆
        ((fun t => t - a) ⁻¹' {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L}) ∪
          ⋃ i, {t : ι → ℝ | t i = a i} := by
      intro t ht
      by_cases h : ∃ i, t i = a i
      · exact Or.inr (Set.mem_iUnion.2 h)
      · push Not at h
        refine Or.inl ⟨fun i => ?_, ht.2⟩
        exact sub_pos.2 (lt_of_le_of_ne (ht.1 i) (h i).symm)
    have hnull : volume (⋃ i, {t : ι → ℝ | t i = a i}) = 0 :=
      measure_iUnion_null fun i => Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i (a i)
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    rw [hnull, add_zero]
    simp only [sub_eq_add_neg]
    rw [measure_preimage_add_right]
    exact volume_pos_simplex_le ι L hL

end GlobalTheory.SimplexVolume
