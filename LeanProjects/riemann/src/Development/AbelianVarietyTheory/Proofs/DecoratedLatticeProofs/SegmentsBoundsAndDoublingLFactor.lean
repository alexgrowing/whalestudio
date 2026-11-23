import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun

theorem prod_map_sum {ι : Type} (s : Finset ι) (m : ι → Multiset ℂˣ) (F : ℂˣ → ℂ) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]

variable {K : Type} [Field K] [NumberField K]

theorem prod_fin_eq {N k t : ℕ} (w : HeightOneSpectrum (𝓞 K)) (z : ℕ → ℂˣ) (α : Fin N → ℂˣ)
    (hα : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, seg w (z i) t) (F : ℂˣ → ℂ) :
    ∏ j, F (α j) =
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range t, F (z i * npowU w (((t : ℂ) - 1) / 2 - l)) := by
  rw [Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun j => F (α j)) = (Finset.univ.val.map α).map F from
      (Multiset.map_map _ _ _).symm, hα, prod_map_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [seg, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

theorem re_exp (t l : ℕ) : (((t : ℂ) - 1) / 2 - l).re = ((t : ℝ) - 1) / 2 - l := by
  simp

theorem npow_neg_nat (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    npow w (-(m : ℂ)) = (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ m)⁻¹ := by
  rw [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem prod_Icc_one (t : ℕ) (g : ℕ → ℂ) : ∏ n ∈ Finset.Icc 1 t, g n = ∏ l ∈ Finset.range t, g (l + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun l _ => by rw [add_comm]

theorem entry_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) (t l : ℕ) :
    ((z * npowU w (((t : ℂ) - 1) / 2 - l) : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (l + 1))⁻¹ := by
  rw [Units.val_mul, coe_npowU, mul_assoc, show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
    npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  congr 2
  push_cast
  ring

theorem entry_inv_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) {t l : ℕ} (hl : l < t) :
    (((z * npowU w (((t : ℂ) - 1) / 2 - l))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ)⁻¹ * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (t - 1 - l + 1))⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_mul, coe_npowU, mul_inv, mul_assoc,
    show (npow w (((t : ℂ) - 1) / 2 - l))⁻¹ = npow w (-(((t : ℂ) - 1) / 2 - l)) by
      rw [npow, npow, Complex.cpow_neg],
    show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  have e : ((t - 1 - l + 1 : ℕ) : ℂ) = t - l := by
    rw [show t - 1 - l + 1 = t - l by omega, Nat.cast_sub hl.le]
  rw [e]
  congr 2
  ring

end GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun GlobalTheory.LFun.SegFactor in
theorem GlobalTheory.LFun.seg_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  intro K _ _ w k t N z hz α hα
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm w
  have mem : ∀ j, ∃ i ∈ Finset.Icc 1 k, ∃ l < t, α j = z i * npowU w (((t : ℂ) - 1) / 2 - l) := by
    intro j
    have h1 : α j ∈ Finset.univ.val.map α := Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    rw [hα] at h1
    obtain ⟨i, hi, h2⟩ := Multiset.mem_sum.1 h1
    obtain ⟨l, hl, e⟩ := Multiset.mem_map.1 h2
    exact ⟨i, hi, l, Finset.mem_range.1 hl, e.symm⟩
  refine ⟨fun j => ?_, ?_⟩
  · obtain ⟨i, -, l, hl, e⟩ := mem j
    have hn : ‖(α j : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2 - l) := by
      rw [e, Units.val_mul, norm_mul, hz, one_mul, coe_npowU, norm_npow, re_exp]
    have hl' : (l : ℝ) + 1 ≤ t := by exact_mod_cast hl
    have h0 : (0 : ℝ) ≤ l := l.cast_nonneg
    rw [hn, ← Real.rpow_neg (by linarith)]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hN.le (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)⟩
  · have eA : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor, prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - (β : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [entry_mul]
    have eB : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor]
      refine (prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - ((β⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)).trans ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹),
        ← Finset.prod_range_reflect (fun l => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ (l + 1))⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [entry_inv_mul w (z i) (Finset.mem_range.1 hl)]
    rw [eA, eB, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [mul_inv]
