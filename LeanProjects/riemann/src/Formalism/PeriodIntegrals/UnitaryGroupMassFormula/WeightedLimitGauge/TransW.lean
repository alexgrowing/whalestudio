import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

def boost (y : Fin k → ℂ) (c : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  Fin.lastCases (Fin.lastCases c (fun j' => ((‖c‖ : ℂ) / conj c) * conj (y j')) j)
    (fun i' => Fin.lastCases (y i')
      (fun j' => (if i' = j' then 1 else 0) + y i' * conj (y j') / (1 + (‖c‖ : ℂ))) j) i

theorem form_apply (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Aᴴ * Hb k * A) i j = ∑ l : Fin k, conj (A l.castSucc i) * A l.castSucc j -
      conj (A (Fin.last k) i) * A (Fin.last k) j := by
  rw [Hb, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def, Fin.castSucc_ne_last, if_false,
    if_true, mul_one]
  ring

theorem boost_mem (y : Fin k → ℂ) (c : ℂ)
    (hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1) (hc0 : c ≠ 0) :
    (boost y c)ᴴ * Hb k * boost y c = Hb k := by
  have hc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hD : (1 + ((‖c‖ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [norm_nonneg c]
  have hcc : conj c ≠ 0 := by rwa [map_ne_zero]
  have hn0 : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hc0
  have hcb : conj c = ((‖c‖ : ℝ) : ℂ) ^ 2 / c := by
    rw [eq_div_iff hc0]; exact hc
  ext i j
  rw [form_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_eq, if_true]
      rw [hS, hc]; ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last j).symm]
      have h1 : ∀ l : Fin k, conj (y l) * ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = j then conj (y l) else 0) + (conj (y j) / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last i)]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) * y l =
          (if l = i then y l else 0) + (y i / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l
        simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        split_ifs <;> simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply, Fin.castSucc_inj,
        Fin.castSucc_ne_last, if_false]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) *
          ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = i then (if i = j then 1 else 0) else 0) + (if l = i then y i * conj (y j) / (1 + (‖c‖ : ℂ)) else 0) +
            (if l = j then conj (y l) * y i / (1 + (‖c‖ : ℂ)) else 0) +
            (y i * conj (y j) / (1 + (‖c‖ : ℂ)) ^ 2) * (conj (y l) * y l) := by
        intro l
        simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        by_cases hi : l = i <;> by_cases hj : l = j
        · subst hi; subst hj; simp <;> field_simp <;> ring
        · subst hi; simp [hj] <;> field_simp <;> ring
        · subst hj; simp [hi] <;> field_simp <;> ring
        · simp [hi, hj] <;> field_simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      split_ifs with hij
      · subst hij; try simp only [hcb]; field_simp; ring
      · try simp only [hcb]; field_simp; ring

theorem hermHb_self (v : Fin (k + 1) → ℂ) :
    herm (Hb k) v v = ((∑ l : Fin k, Complex.normSq (v l.castSucc) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  unfold herm
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [Hb, Matrix.mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, Pi.star_apply, Complex.star_def]
  push_cast [Complex.normSq_eq_conj_mul_self]
  ring

theorem emb_mulVec_out (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) : (embWb k r μ *ᵥ v) i = v i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · unfold embWb
    rw [dif_neg (by omega), if_pos ⟨rfl, by omega⟩, one_mul]
  · intro l _ hl
    unfold embWb
    rw [dif_neg (by omega), if_neg (fun h => hl h.1.symm), zero_mul]
  · simp

theorem wLast_inWb (s : ℂ) : inWb k r (s • wLast k r) := by
  intro i hi
  have : i ≠ wI k r (Fin.last k) := by
    intro h; have := congrArg Fin.val h; simp only [wI, Fin.val_last] at this; omega
  simp [wLast, bvec, Pi.single_apply, this]

theorem wbPart_wLast (s : ℂ) (m : Fin (k + 1)) :
    wbPart k r (s • wLast k r) m = if m = Fin.last k then s else 0 := by
  simp only [wbPart, wLast, bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : m = Fin.last k
  · subst h; simp
  · rw [if_neg (fun h' => h (wI_injective h')), if_neg h, mul_zero]

theorem transW : TransW := by
  intro k r z hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := Real.sqrt T with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hss : s * s = T := Real.mul_self_sqrt hT.le
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  set u : Fin (k + 1) → ℂ := fun j => z (wI k r j) / s with hu
  set y : Fin k → ℂ := fun l => u l.castSucc with hy
  set c : ℂ := u (Fin.last k) with hcdef

  have hTform : T = Complex.normSq (z (wI k r (Fin.last k))) - ∑ l : Fin k, Complex.normSq (z (wI k r l.castSucc)) := by
    rw [hTdef, Tz, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]
    simp only [wbPart]; ring
  have hnq : ∀ a : ℂ, Complex.normSq (a / s) = Complex.normSq a / T := by
    intro a; rw [Complex.normSq_div, Complex.normSq_ofReal, hss]
  have hBA : Complex.normSq c - ∑ l : Fin k, Complex.normSq (y l) = 1 := by
    simp only [hcdef, hy, hu, hnq]
    rw [← Finset.sum_div, ← sub_div, ← hTform, div_self hT.ne']
  have hA0 : 0 ≤ ∑ l : Fin k, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hBA; linarith
  have hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e1 : ∑ l, conj (y l) * y l = ((∑ l : Fin k, Complex.normSq (y l) : ℝ) : ℂ) := by
      push_cast [Complex.normSq_eq_conj_mul_self]; rfl
    have e2 : (‖c‖ : ℝ) ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    have hA : ∑ l : Fin k, Complex.normSq (y l) = Complex.normSq c - 1 := by linarith
    rw [e1, ← Complex.ofReal_pow, e2, hA]
    push_cast; ring
  refine ⟨embWb k r (boost y c), MB.emb_mem_UWb (boost_mem y c hS hc0), ?_⟩
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [emb_mulVec_out _ _ i hi, wLast_inWb _ i hi, hz i hi]
  · push Not at hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin (k + 1), wI k r j = i :=
      ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    have e := congrFun (wbPart_emb (boost y c) _ (wLast_inWb (k := k) (r := r) (s : ℂ))) j
    simp only [wbPart] at e
    rw [e, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last k)]
    · have hb : boost y c j (Fin.last k) = u j := by
        induction j using Fin.lastCases with
        | last => simp [boost, hcdef]
        | cast j' => simp [boost, hy]
      have hw := wbPart_wLast (k := k) (r := r) (s : ℂ) (Fin.last k)
      rw [hb, hw, if_pos rfl]
      simp only [hu]
      field_simp
    · intro m _ hm
      have hw := wbPart_wLast (k := k) (r := r) (s : ℂ) m
      rw [hw, if_neg hm, mul_zero]
    · simp

end PI.RhsWLim.W
