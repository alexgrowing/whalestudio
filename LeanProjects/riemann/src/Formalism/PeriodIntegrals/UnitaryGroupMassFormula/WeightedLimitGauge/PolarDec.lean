import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.UnimodS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.BallConj

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem hpk_mulVec_gen (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = HU.sgn k r i * v (HU.tau k r i) := hpk_mulVec_apply v i

theorem herm_bvec (u : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) u (bvec i) = (Hpk k r *ᵥ u) i := by
  unfold herm bvec
  have : star (Pi.single i (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single i (1 : ℂ) := by
    funext j; simp [Pi.single_apply]
  rw [this, single_dotProduct, one_mul]

theorem herm_pres {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (p *ᵥ u) (p *ᵥ v) = herm (Hpk k r) u v := by
  rw [herm_mulVec_right hp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (HU.isUnit_of_uh hp), Matrix.one_mulVec]

theorem uwb_emb {p : Mat k r} (hp : p ∈ UWb k r) :
    p = embWb k r (fun i j => p (wI k r i) (wI k r j)) := by
  ext i j
  by_cases hj : j.val < r ∨ r + k < j.val
  ·
    have hcol : p *ᵥ bvec j = bvec j := by
      rcases hj with hj | hj
      · have := (hp.2 ⟨j.val, hj⟩).1
        have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
        rwa [e] at this
      · have := (hp.2 ⟨2 * r + k - j.val, by omega⟩).2
        have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rwa [e] at this
    have h1 := congrFun hcol i
    rw [MB.mulVec_bvec, MB.bvec_apply] at h1
    rw [h1]
    unfold embWb
    rw [dif_neg (by omega)]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos ⟨rfl, by omega⟩]
    · rw [if_neg hij, if_neg (fun h => hij h.1)]
  · push Not at hj
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (k + 1), wI k r j' = j :=
      ⟨⟨j.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    by_cases hi : i.val < r ∨ r + k < i.val
    ·
      have hw : (p *ᵥ bvec (wI k r j')) i = 0 := by
        rcases hi with hi | hi
        ·
          set a : Fin r := ⟨i.val, hi⟩
          have hfix := (hp.2 a).2
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (esI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (esI k r a) = i := by
            unfold HU.tau esI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (esI k r a) = 1 := by
            unfold HU.sgn esI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
        · set a : Fin r := ⟨2 * r + k - i.val, by omega⟩
          have hfix := (hp.2 a).1
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (eI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (eI k r a) = i := by
            unfold HU.tau eI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (eI k r a) = 1 := by
            unfold HU.sgn eI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
      rw [MB.mulVec_bvec] at hw
      rw [hw]
      unfold embWb
      rw [dif_neg (by omega), if_neg (fun h => by have := congrArg Fin.val h.1; simp only [wI] at this; omega)]
    · push Not at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (k + 1), wI k r i' = i :=
        ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
      have := embWb_wI (k := k) (r := r) (fun i j => p (wI k r i) (wI k r j)) i' j'
      exact this.symm

theorem col_unitary (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hμ : μᴴ * Hb k * μ = Hb k) (l : ℂ)
    (hl : conj l * l = 1) (hcol : ∀ i, μ i (Fin.last k) = if i = Fin.last k then l else 0) : μᴴ * μ = 1 := by
  have hl0 : conj l ≠ 0 := by intro h; rw [h, zero_mul] at hl; exact zero_ne_one hl
  have hrow : ∀ j, j ≠ Fin.last k → μ (Fin.last k) j = 0 := by
    intro j hj
    have h := congrFun (congrFun hμ (Fin.last k)) j
    rw [form_apply] at h
    simp only [hcol, Fin.castSucc_ne_last, if_false, map_zero, zero_mul, Finset.sum_const_zero, if_true,
      zero_sub, Hb, Matrix.diagonal_apply_ne _ (Ne.symm hj)] at h
    have : conj l * μ (Fin.last k) j = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left hl0
  have key : ∀ i j, (μᴴ * μ) i j = Hb k i j + 2 * (conj (μ (Fin.last k) i) * μ (Fin.last k) j) := by
    intro i j
    have h := congrFun (congrFun hμ i) j
    rw [form_apply] at h
    rw [← h, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    ring
  ext i j
  rw [key]
  by_cases hi : i = Fin.last k
  · by_cases hj : j = Fin.last k
    · subst hi; subst hj
      rw [hcol, if_pos rfl, hl]
      simp [Hb]; norm_num
    · rw [hrow j hj, mul_zero, mul_zero, add_zero, Hb, Matrix.diagonal_apply_ne _ (fun h => hj (h.symm.trans hi)),
        Matrix.one_apply_ne (fun h => hj (h.symm.trans hi))]
  · rw [hrow i hi, map_zero, zero_mul, mul_zero, add_zero, Hb, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; exact hi (h1 ▸ h2))

theorem boost_herm (y : Fin k → ℂ) (n : ℝ) (hn : 0 < n) : (boost y (n : ℂ))ᴴ = boost y (n : ℂ) := by
  have hnn : ‖(n : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  ext i j
  rw [Matrix.conjTranspose_apply, Complex.star_def]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [boost]
    | cast j => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
    | cast j =>
      simp only [boost, Fin.lastCases_castSucc, hnn, map_add, map_div₀, map_mul, Complex.conj_conj,
        Complex.conj_ofReal, map_one]
      by_cases h : i = j
      · subst h; simp; ring
      · rw [if_neg (Ne.symm h), if_neg h]; simp; ring

theorem polarDecW : PolarDecW := by
  intro k r p hp
  set μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j => p (wI k r i) (wI k r j) with hμdef
  have hpμ : p = embWb k r μ := uwb_emb hp
  have hμ : μᴴ * Hb k * μ = Hb k := (MB.emb_mem μ).1 (hpμ ▸ hp.1)
  set y : Fin k → ℂ := fun l => μ l.castSucc (Fin.last k) with hy
  set c : ℂ := μ (Fin.last k) (Fin.last k) with hc
  have hform := congrFun (congrFun hμ (Fin.last k)) (Fin.last k)
  rw [form_apply] at hform
  have hS0 : ∑ l, conj (y l) * y l = conj c * c - 1 := by
    simp only [Hb, Matrix.diagonal_apply_eq, if_true] at hform
    simp only [hy, hc]; linear_combination hform
  have hA : ∑ l, conj (y l) * y l = ((∑ l, Complex.normSq (y l) : ℝ) : ℂ) := by
    push_cast [Complex.normSq_eq_conj_mul_self]; rfl
  have hA0 : 0 ≤ ∑ l, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hcc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul, zero_sub, hA] at hS0
    have := congrArg Complex.re hS0
    simp at this; linarith
  set n : ℝ := ‖c‖ with hn
  have hnpos : 0 < n := norm_pos_iff.2 hc0
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hnpos.ne'
  set y' : Fin k → ℂ := fun l => y l * ((n : ℂ) / c) with hy'
  have hnn : ‖((n : ℝ) : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  have hS' : ∑ l, conj (y' l) * y' l = ((‖((n : ℝ) : ℂ)‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e : ∀ l, conj (y' l) * y' l = conj (y l) * y l * (((n : ℂ) ^ 2) / (conj c * c)) := by
      intro l; simp only [hy', map_mul, map_div₀, Complex.conj_ofReal]; field_simp
    simp only [e, ← Finset.sum_mul, hS0, hcc, hnn]
    field_simp
  set B₀ := boost y' (n : ℂ) with hB₀
  have hB : B₀ᴴ * Hb k * B₀ = Hb k := boost_mem y' (n : ℂ) hS' hn0
  have hBh : B₀ᴴ = B₀ := boost_herm y' n hnpos
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  set Bi := Hb k * B₀ᴴ * Hb k with hBi
  have hBiB : Bi * B₀ = 1 := by
    calc Bi * B₀ = Hb k * (B₀ᴴ * Hb k * B₀) := by simp only [hBi, Matrix.mul_assoc]
      _ = 1 := by rw [hB, hb_sq]
  have hBBi : B₀ * Bi = 1 := mul_eq_one_comm.mp hBiB
  have hBHB : B₀ * Hb k * B₀ᴴ = Hb k := by
    have : B₀ * Hb k * B₀ᴴ * Hb k = 1 := by rw [← hBBi, hBi]; simp only [Matrix.mul_assoc]
    calc B₀ * Hb k * B₀ᴴ = B₀ * Hb k * B₀ᴴ * Hb k * Hb k := by rw [Matrix.mul_assoc (B₀ * Hb k * B₀ᴴ) (Hb k) (Hb k), hb_sq, Matrix.mul_one]
      _ = Hb k := by rw [this, Matrix.one_mul]
  set μq := Bi * μ with hμq
  have hμqU : μqᴴ * Hb k * μq = Hb k := by
    have hBi' : Biᴴ * Hb k * Bi = Hb k := by
      simp only [hBi, Matrix.conjTranspose_mul, hHbh, conjTranspose_conjTranspose]
      calc Hb k * (B₀ * Hb k) * Hb k * (Hb k * B₀ᴴ * Hb k) = Hb k * (B₀ * (Hb k * Hb k) * Hb k * B₀ᴴ) * Hb k := by
            simp only [Matrix.mul_assoc]
        _ = Hb k := by rw [hb_sq, Matrix.mul_one, hBHB, hb_sq, Matrix.one_mul]
    calc μqᴴ * Hb k * μq = μᴴ * (Biᴴ * Hb k * Bi) * μ := by
          simp only [hμq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hb k := by rw [hBi', hμ]
  set e : ℂ := c / n with he
  have hucol : ∀ l, μ l (Fin.last k) = e * B₀ l (Fin.last k) := by
    intro l
    induction l using Fin.lastCases with
    | last => simp only [hB₀, boost, Fin.lastCases_last, he, hc]; field_simp
    | cast j => simp only [hB₀, boost, Fin.lastCases_last, Fin.lastCases_castSucc, he, hy', hy]; field_simp
  have hcol : ∀ i, μq i (Fin.last k) = if i = Fin.last k then e else 0 := by
    intro i
    have : μq i (Fin.last k) = e * (Bi * B₀) i (Fin.last k) := by
      simp only [hμq, Matrix.mul_apply, hucol, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, hBiB, Matrix.one_apply]
    split_ifs <;> simp
  have he1 : conj e * e = 1 := by
    simp only [he, map_div₀, Complex.conj_ofReal]
    rw [div_mul_div_comm, hcc]
    field_simp
  have hqu := col_unitary μq hμqU e he1 hcol
  refine ⟨B₀, hB, hBh, embWb k r μq, MB.emb_mem_UWb hμqU, ?_, ?_⟩
  · rw [MB.emb_conjT, ← MB.emb_mul, hqu, MB.emb_one]
  · rw [← MB.emb_mul, hμq, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, ← hpμ]

theorem unimodW : UnimodW := unimodW_of_two ballConj polarDecW

end PI.RhsWLim.W
