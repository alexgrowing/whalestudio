import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0TruncatedExplicitFormula
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.GoodBound

theorem inv_eq_self_of_real {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero q] (h : GlobalTheoryTheory.IsRealChar χ) :
    χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  exact Complex.conj_eq_iff_im.2 (h _)

theorem re_bounds {Q T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 T) : 1 / 400 ≤ ρ.re ∧ ρ.re ≤ 1 - 1 / 400 := by
  obtain ⟨hp, hr, -, hz⟩ := hg
  obtain ⟨h0, h1, h2, h3⟩ := hρ
  rw [sub_zero] at h2
  refine ⟨?_, not_lt.1 fun h => hz ρ h (h2.trans hT) h3⟩
  by_contra hlt
  have h4 := (zeros_symm_one_sub q χ hp ρ h0 h1).1.1 h3
  rw [inv_eq_self_of_real χ hr] at h4
  refine hz (1 - ρ) ?_ ?_ h4
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [not_le.1 hlt]
  · simpa using h2.trans hT

theorem recip_le {Q T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 T) : 1 / ‖ρ‖ ≤ 400 := by
  have h1 := (re_bounds hg hT hρ).1
  have h2 : ρ.re ≤ ‖ρ‖ := Complex.re_le_norm ρ
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem low_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hQ : 1 ≤ Q) : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf, zsumR_eq_sum_toFinset χ _ _ _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := recip_le hg hQ (by simpa using hρ : ρ ∈ zerosIn χ 0 1)
  have h0 : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  nlinarith

theorem low_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf]
  exact Finset.sum_nonneg fun ρ _ => by positivity

theorem norm_zsum_le {Q T u : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) (hu : 1 ≤ u) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ u ^ (1 - (1 : ℝ) / 400) *
      (zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) + 400 * zsumR χ 0 1 (fun _ => 1)) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hA : 0 ≤ u ^ (1 - (1 : ℝ) / 400) := by positivity
  have hI := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (by norm_num))) hA)
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  unfold zsum
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have h2 : ‖(u : ℂ) ^ ρ / ρ‖ ≤ u ^ (1 - (1 : ℝ) / 400) * (1 / ‖ρ‖) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hu (re_bounds hg hT hρ').2) (by positivity)
  have h3 : 1 / ‖ρ‖ ≤ (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) +
      400 * (if ρ ∈ zerosIn χ 0 1 then (1 : ℝ) else 0) := by
    by_cases h : 1 < |ρ.im|
    · rw [if_pos h]
      split_ifs <;> simp
    · have : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by simpa using h, hρ'.2.2.2⟩
      rw [if_neg h, if_pos this]
      linarith [recip_le hg hT hρ']
  have h0 : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  rw [norm_mul, Complex.norm_natCast]
  calc _ ≤ (zmult χ ρ : ℝ) * (u ^ (1 - (1 : ℝ) / 400) * ((if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) +
      400 * (if ρ ∈ zerosIn χ 0 1 then (1 : ℝ) else 0))) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hA)) h0
    _ = _ := by ring

set_option maxHeartbeats 1000000 in

theorem psiChi_bound_of_goodFor : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, 2 ≤ u → ‖psiChi χ u‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2) := by
  intro hE hL hZ _ hE0
  obtain ⟨C, hC⟩ := ExplUsed.explicit_formula_used hE0 hE hL
  obtain ⟨D, hD⟩ := zsumR_recip_le hZ
  refine ⟨|C| * (5 + 800 * |D|) + 801 * |D| + 1, by positivity, ?_⟩
  intro Q q _ χ hQ hχ hg u hu
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqQ : (q : ℝ) ≤ Q := hg.2.2.1
  obtain ⟨T, hT2, hTu, hTQ, huT⟩ : ∃ T : ℝ, 2 ≤ T ∧ T ≤ u ∧ T ≤ Q ∧ u / T ≤ 1 + u / Q := by
    have : 0 ≤ u / Q := by positivity
    rcases le_total u Q with h | h
    · exact ⟨u, hu, le_rfl, h, by rw [div_self (by linarith)]; linarith⟩
    · exact ⟨Q, by linarith, h, le_rfl, by linarith⟩
  have h1 := hC q χ hg.1 u T hT2 hTu
  obtain ⟨h2, h3⟩ := hD q χ hg.1 T hT2
  have h4 := norm_zsum_le hg hTQ (by linarith : (1 : ℝ) ≤ u)
  have h5 := low_le hg (by linarith : (1 : ℝ) ≤ Q)
  have h6 := low_nonneg χ
  have hpsi : GlobalTheoryTheory.psi0 χ u = psiChi χ u := by
    simp [GlobalTheoryTheory.psi0, psiChi, hχ]
  rw [hpsi] at h1
  set S := zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
  set A := u ^ (1 - (1 : ℝ) / 400)
  set L := Real.log (u * Q) with hLdef
  set N := zsumR χ 0 1 (fun _ => (1 : ℝ))
  set R := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)
  set H := zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
  have hA1 : 1 ≤ A := Real.one_le_rpow (by linarith) (by norm_num)
  have hP : 6 ≤ u * Q := by nlinarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h2L : Real.log ((u * Q) ^ 2) = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
  have l1 : Real.log (q * T) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by nlinarith))
      (Real.log_le_log (by nlinarith) (by nlinarith)) 2
  have hqu : (q : ℝ) * u ≤ u * Q := by nlinarith
  have hqu1 : (1 : ℝ) ≤ q * u := by nlinarith
  have l2 : Real.log (3 * q) ≤ 2 * L := by
    rw [← h2L]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have l2' : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have l3 : Real.log (q * u) ≤ L := Real.log_le_log (by linarith) hqu
  have l3' : 0 ≤ Real.log (q * u) := Real.log_nonneg hqu1
  have l4 : Real.log (q * u * T) ^ 2 ≤ (2 * L) ^ 2 := by
    refine pow_le_pow_left₀ (Real.log_nonneg (by nlinarith)) ?_ 2
    rw [← h2L, sq]
    exact Real.log_le_log (by positivity)
      (mul_le_mul hqu (by nlinarith) (by linarith) (by linarith))
  have hB : 0 ≤ u / Q := by positivity
  set B := u / Q
  have hD0 := abs_nonneg D
  have hC0 := abs_nonneg C
  have hM : 0 ≤ L ^ 2 := sq_nonneg _
  have hN : N ≤ 2 * (|D| * L ^ 2) := by
    have := h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) l2').trans
      (mul_le_mul_of_nonneg_left (l2.trans (by linarith : 2 * L ≤ 2 * L ^ 2)) hD0))
    linarith
  have hH : H ≤ |D| * L ^ 2 :=
    h2.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left l1 hD0))
  have hS : ‖S‖ ≤ A * (801 * (|D| * L ^ 2)) :=
    h4.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have e1 : u * Real.log (q * u * T) ^ 2 / T ≤ (1 + B) * (2 * L) ^ 2 := by
    rw [mul_div_right_comm]
    exact mul_le_mul huT l4 (sq_nonneg _) (by linarith)
  have e0 : 0 ≤ u * Real.log (q * u * T) ^ 2 / T := by positivity
  set M := L ^ 2
  have hAM : M ≤ A * M := le_mul_of_one_le_left hM hA1
  have hBM : 0 ≤ B * M := mul_nonneg hB hM
  have hDM : |D| * M ≤ |D| * (A * M + B * M) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have hDM' : |D| * (A * M) ≤ |D| * (A * M + B * M) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have e2 : u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + R ≤
      (5 + 800 * |D|) * (A * M + B * M) := by
    have : (1 + B) * (2 * L) ^ 2 = 4 * M + 4 * (B * M) := by simp only [M]; ring
    have h7 : (5 + 800 * |D|) * (A * M + B * M) = 5 * (A * M) + 5 * (B * M) + 800 * (|D| * (A * M + B * M)) := by
      ring
    linarith
  have e3 := h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)).trans
    (mul_le_mul_of_nonneg_left e2 hC0))
  have htri : ‖psiChi χ u‖ ≤ ‖psiChi χ u + S‖ + ‖S‖ := by
    simpa using norm_sub_le (psiChi χ u + S) S
  have h8 : A * (801 * (|D| * M)) = 801 * (|D| * (A * M)) := by ring
  have h9 : (|C| * (5 + 800 * |D|) + 801 * |D| + 1) * (A * M + B * M) =
      |C| * ((5 + 800 * |D|) * (A * M + B * M)) + 801 * (|D| * (A * M + B * M)) + (A * M + B * M) := by ring
  linarith

end GlobalTheory.Mem.An.GoodBound
