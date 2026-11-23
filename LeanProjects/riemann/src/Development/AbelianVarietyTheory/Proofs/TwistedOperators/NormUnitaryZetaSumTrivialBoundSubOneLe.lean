import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.UnitaryBound

open GlobalTheory.LFun

theorem norm_prod_sub_one_le (c : ℝ) (M : Multiset ℂ) (h : ∀ z ∈ M, ‖z - 1‖ ≤ c) :
    ‖M.prod - 1‖ ≤ (1 + c) ^ M.card - 1 := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have h1 := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have h2 := h a (Multiset.mem_cons_self _ _)
    have hc : 0 ≤ c := (norm_nonneg _).trans h2
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have e : a * M.prod - 1 = (a - 1) * (M.prod - 1) + (a - 1) + (M.prod - 1) := by ring
    rw [e]
    have h3 : ‖(a - 1) * (M.prod - 1)‖ ≤ c * ((1 + c) ^ M.card - 1) := by
      rw [norm_mul]; exact mul_le_mul h2 h1 (norm_nonneg _) hc
    have h4 : ‖(a - 1) * (M.prod - 1) + (a - 1) + (M.prod - 1)‖ ≤
        ‖(a - 1) * (M.prod - 1)‖ + ‖a - 1‖ + ‖M.prod - 1‖ :=
      by
        linarith [norm_add_le ((a - 1) * (M.prod - 1) + (a - 1)) (M.prod - 1), norm_add_le ((a - 1) * (M.prod - 1)) (a - 1)]
    nlinarith

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 / 2 ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rw [norm_one] at this
    linarith
  have hne : (1 - y) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    norm_num at h1
  have hm : (1 - y) * (1 - y)⁻¹ = 1 := mul_inv_cancel₀ hne
  have e : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by linear_combination hm
  rw [e, norm_mul, norm_inv]
  have hpos : 0 < ‖1 - y‖ := by linarith
  rw [mul_inv_le_iff₀ hpos]
  nlinarith [norm_nonneg y]

theorem one_add_pow_sub_one_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    (1 + c) ^ n - 1 ≤ (2 ^ n - 1) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    rw [pow_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + c),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) hc0) (sub_nonneg.2 hc1)]

theorem norm_zetaSum_sub_one_le : ∀ (q r t : ℕ), 2 ≤ q → r + 5 ≤ t → ∀ α : Fin (r / 2) → ℂˣ,
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ‖eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) *
      ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q r t hq hrt α hα
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have key : ∀ a b : ℕ, a + 2 ≤ b → (q : ℝ) ^ a * ((q : ℝ) ^ b)⁻¹ ≤ δ := by
    intro a b hab
    obtain ⟨k, rfl⟩ : ∃ k, b = a + 2 + k := ⟨b - (a + 2), by omega⟩
    have hpa : (0 : ℝ) < (q : ℝ) ^ a := by positivity
    rw [show (q : ℝ) ^ (a + 2 + k) = (q : ℝ) ^ a * ((q : ℝ) ^ 2 * (q : ℝ) ^ k) by ring, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hpa.ne', one_mul, hδ]
    apply inv_anti₀ (by positivity)
    have : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ hq1
    nlinarith [show (0 : ℝ) < (q : ℝ) ^ 2 by positivity]
  have hbound : ((q : ℝ) ^ 2) ^ (((r : ℝ) - 1) / 2) ≤ (q : ℝ) ^ r := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hent : ∀ b ∈ bcParam r α, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ r := by
    intro b hb
    simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Finset.mem_univ_val, true_and,
      Multiset.mem_replicate] at hb
    have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨_, rfl⟩
    · exact (hα i).2.trans hbound
    · rw [Units.val_inv_eq_inv_val, norm_inv]
      have hpos : 0 < ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hq2 _
      calc ‖(α i : ℂ)‖⁻¹ ≤ (((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)))⁻¹ := inv_anti₀ hpos (hα i).1
        _ = ((q : ℝ) ^ 2) ^ (((r : ℝ) - 1) / 2) := by rw [Real.rpow_neg hq2.le, inv_inv]
        _ ≤ _ := hbound
    · simp only [Units.val_one, norm_one]
      exact one_le_pow₀ hq1
  set x : ℂ := ((q : ℂ) ^ (t + 1))⁻¹ with hx
  have hxn : ‖x‖ = ((q : ℝ) ^ (t + 1))⁻¹ := by rw [hx, norm_inv, norm_pow, Complex.norm_natCast]
  set M1 : Multiset ℂ := (bcParam r α).map fun b : ℂˣ => (1 - (b : ℂ) * x)⁻¹ with hM1
  set M2 : Multiset ℂ := (Finset.range r).val.map fun j => 1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹ with hM2
  have heq : eulerFac (bcParam r α) x * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) =
      (M1 + M2).prod := by
    rw [Multiset.prod_add, eulerFac_eq_prod]
    rfl
  have hcard : (M1 + M2).card = r + r := by
    simp [hM1, hM2, GlobalTheory.LGrp.card_bcParam]
  have hfac : ∀ z ∈ M1 + M2, ‖z - 1‖ ≤ 2 * δ := by
    intro z hz
    rcases Multiset.mem_add.1 hz with hz | hz
    · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hz
      have hbx : ‖(b : ℂ) * x‖ ≤ δ := by
        rw [norm_mul, hxn]
        exact (mul_le_mul_of_nonneg_right (hent b hb) (by positivity)).trans (key r (t + 1) (by omega))
      exact (norm_inv_one_sub_sub_one_le (by linarith)).trans (by linarith)
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hz
      have hj' : j < r := Finset.mem_range.1 hj
      have : ‖(1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1‖ = (q : ℝ) ^ j * ((q : ℝ) ^ (r + t))⁻¹ := by
        rw [sub_sub_cancel_left, norm_neg, norm_mul, norm_inv, norm_pow, norm_pow, norm_neg, Complex.norm_natCast]
      rw [this]
      linarith [key j (r + t) (by omega)]
  rw [heq]
  refine (norm_prod_sub_one_le _ _ hfac).trans ?_
  rw [hcard]
  refine (one_add_pow_sub_one_le (by linarith) (by linarith) _).trans ?_
  have h4 : (2 : ℝ) ^ (r + r) = 4 ^ r := by rw [← two_mul, pow_mul]; norm_num
  have ha : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num)
  have h16 : (16 : ℝ) ^ r = (4 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h27 : (16 : ℝ) ^ r ≤ 27 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
  have hk : 2 * ((4 : ℝ) ^ r - 1) ≤ 27 ^ r := by nlinarith
  rw [h4]
  calc ((4 : ℝ) ^ r - 1) * (2 * δ) = (2 * ((4 : ℝ) ^ r - 1)) * δ := by ring
    _ ≤ 27 ^ r * δ := mul_le_mul_of_nonneg_right hk hδ0

end GlobalTheory.FinZeta.UnitaryBound

end
