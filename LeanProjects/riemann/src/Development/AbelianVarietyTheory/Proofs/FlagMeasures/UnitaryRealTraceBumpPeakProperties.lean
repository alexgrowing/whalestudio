import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem sum_normSq_col {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (i : Fin n) :
    ∑ j, ‖g j i‖ ^ 2 = 1 := by
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg
  have h2 : (star g * g) i i = 1 := by rw [h1]; simp
  rw [Matrix.mul_apply] at h2
  have h3 : ((∑ j, ‖g j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h3

theorem norm_entry_le_one {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (j i : Fin n) :
    ‖g j i‖ ≤ 1 := by
  have h := sum_normSq_col hg i
  have h2 : ‖g j i‖ ^ 2 ≤ ∑ j, ‖g j i‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖g j i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  rw [h] at h2
  nlinarith [norm_nonneg (g j i)]

theorem re_trace_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace g).re = ∑ i, (g i i).re := by
  simp [Matrix.trace, Complex.re_sum]

theorem eq_one_of_re_trace {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))
    (ht : (Matrix.trace g).re = n) : g = 1 := by
  have hle : ∀ i, (g i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans (norm_entry_le_one hg i i)
  have hsum : ∑ i : Fin n, (1 - (g i i).re) = 0 := by
    rw [Finset.sum_sub_distrib, ← re_trace_eq, ht]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))).1 hsum
  have hre : ∀ i, (g i i).re = 1 := fun i => by
    have := hz i (Finset.mem_univ i)
    linarith
  have hnorm : ∀ i, ‖g i i‖ = 1 := fun i => le_antisymm (norm_entry_le_one hg i i)
    (by simpa [hre i] using Complex.re_le_norm (g i i))
  have hdiag : ∀ i, g i i = 1 := fun i => by
    have h1 : ‖g i i‖ ^ 2 = (g i i).re ^ 2 + (g i i).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hnorm i, hre i] at h1
    have him : (g i i).im = 0 := by nlinarith
    exact Complex.ext (by simpa using hre i) (by simpa using him)
  ext j i
  by_cases hji : j = i
  · subst hji
    simp [hdiag j]
  · have hs := sum_normSq_col hg i
    have h0 : ∑ k ∈ Finset.univ.erase i, ‖g k i‖ ^ 2 = 0 := by
      have := Finset.add_sum_erase Finset.univ (fun k => ‖g k i‖ ^ 2) (Finset.mem_univ i)
      rw [hs, hnorm i] at this
      linarith
    have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h0
    have := hz2 j (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
    have hn : ‖g j i‖ = 0 := by simpa using this
    rw [Matrix.one_apply_ne hji]
    exact norm_eq_zero.1 hn

theorem peak_continuous (n : ℕ) : Continuous (peak n) := by
  unfold peak
  have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace g).re :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  fun_prop

theorem peak_one {n : ℕ} (hn : 0 < n) : peak n 1 = 1 := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [peak, Matrix.trace_one, this]

theorem abs_re_trace_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    |(Matrix.trace g).re| ≤ n := by
  rw [re_trace_eq]
  calc |∑ i, (g i i).re| ≤ ∑ i, |(g i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (norm_entry_le_one hg i i)
    _ = n := by simp

theorem peak_mem_Icc {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    0 ≤ peak n g ∧ peak n g ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_le.1 (abs_re_trace_le hg)
  have h1 : -1 ≤ (Matrix.trace g).re / n := by
    rw [le_div_iff₀ hn']; linarith [h.1]
  have h2 : (Matrix.trace g).re / n ≤ 1 := by
    rw [div_le_iff₀ hn']; linarith [h.2]
  unfold peak
  constructor <;> linarith

theorem peak_lt_one {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (h1 : g ≠ 1) :
    peak n g < 1 := by
  refine lt_of_le_of_ne (peak_mem_Icc hn hg).2 fun he => h1 (eq_one_of_re_trace hg ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold peak at he
  have : (Matrix.trace g).re / n = 1 := by linarith
  field_simp at this
  linarith

theorem peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧
    (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
      0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧
    ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1,
      ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
        g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  intro n hn
  refine ⟨peak_continuous n, peak_one hn, fun g hg => peak_mem_Icc hn hg, fun U hU => ?_⟩
  have hK : IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) :=
    (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).inter_right isOpen_interior.isClosed_compl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  rcases Set.eq_empty_or_nonempty
      ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) with he | hne
  · refine ⟨0, by norm_num, fun g hg hgU => ?_⟩
    have : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ :=
      ⟨hg, fun hi => hgU (interior_subset hi)⟩
    rw [he] at this
    exact this.elim
  · obtain ⟨g₀, hg₀, hmax⟩ := hK.exists_isMaxOn hne (peak_continuous n).continuousOn
    have hne1 : g₀ ≠ 1 := fun h => hg₀.2 (h ▸ h1)
    refine ⟨peak n g₀, peak_lt_one hn hg₀.1 hne1, fun g hg hgU => ?_⟩
    exact hmax ⟨hg, fun hi => hgU (interior_subset hi)⟩

end GlobalTheory.KFinAvg
