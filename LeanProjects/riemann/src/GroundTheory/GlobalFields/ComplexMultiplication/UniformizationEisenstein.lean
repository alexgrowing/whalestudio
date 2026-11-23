import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.Uniformization
import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationAddition

open Complex Filter Topology Set
open scoped PeriodPair Nat

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

def weierstrassCoeff {R : Type*} [CommRing R] [Algebra ℚ R] (a b : R) : ℕ → R
  | 0 => 0
  | 1 => (1 / 20 : ℚ) • a
  | 2 => (1 / 28 : ℚ) • b
  | n + 3 => (3 / ((2 * ((n : ℚ) + 3) + 3) * ((n : ℚ) + 1)) : ℚ) •
      ∑ i : Fin (n + 1), weierstrassCoeff a b (i + 1) * weierstrassCoeff a b (n + 1 - i)
decreasing_by
  all_goals (have := i.isLt; omega)

section Recursion

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

@[simp] lemma weierstrassCoeff_zero (a b : R) : weierstrassCoeff a b 0 = 0 := by
  rw [weierstrassCoeff]

@[simp] lemma weierstrassCoeff_one (a b : R) : weierstrassCoeff a b 1 = (1 / 20 : ℚ) • a := by
  rw [weierstrassCoeff]

@[simp] lemma weierstrassCoeff_two (a b : R) : weierstrassCoeff a b 2 = (1 / 28 : ℚ) • b := by
  rw [weierstrassCoeff]

lemma weierstrassCoeff_add_three (a b : R) (n : ℕ) :
    weierstrassCoeff a b (n + 3) = (3 / ((2 * ((n : ℚ) + 3) + 3) * ((n : ℚ) + 1)) : ℚ) •
      ∑ i : Fin (n + 1), weierstrassCoeff a b (i + 1) * weierstrassCoeff a b (n + 1 - i) := by
  rw [weierstrassCoeff]

theorem weierstrassCoeff_map (f : R →ₐ[ℚ] S) (a b : R) (n : ℕ) :
    f (weierstrassCoeff a b n) = weierstrassCoeff (f a) (f b) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp [map_smul]
    | 2, _ => simp [map_smul]
    | n + 3, ih =>
      rw [weierstrassCoeff_add_three, weierstrassCoeff_add_three, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, ih _ (by have := i.isLt; omega), ih _ (by omega)]

theorem weierstrassCoeff_scale (t a b : R) (n : ℕ) :
    weierstrassCoeff (t ^ 4 * a) (t ^ 6 * b) n = t ^ (2 * n + 2) * weierstrassCoeff a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp
    | n + 3, ih =>
      rw [weierstrassCoeff_add_three, weierstrassCoeff_add_three, mul_smul_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := i.isLt
      rw [ih _ (by omega), ih _ (by omega)]
      have : t ^ (2 * (n + 3) + 2) = t ^ (2 * ((i : ℕ) + 1) + 2) * t ^ (2 * (n + 1 - i) + 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [this]
      ring

end Recursion

def eisensteinPoly (n : ℕ) : MvPolynomial (Fin 2) ℚ :=
  (1 / (2 * (n : ℚ) + 1)) • weierstrassCoeff (MvPolynomial.X 0) (MvPolynomial.X 1) n

lemma aeval_eisensteinPoly (x : Fin 2 → ℂ) (n : ℕ) :
    MvPolynomial.aeval x (eisensteinPoly n) =
      weierstrassCoeff (x 0) (x 1) n / (2 * n + 1) := by
  rw [eisensteinPoly, map_smul, weierstrassCoeff_map, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    Rat.smul_def]
  push_cast
  ring

variable {L : PeriodPair}

variable (L) in

def weierstrassLaurentCoeff (j : ℕ) : ℂ := if j = 0 then 0 else (j + 1) * L.G (j + 2)

lemma weierstrassLaurentCoeff_odd (i : ℕ) : weierstrassLaurentCoeff L (2 * i + 1) = 0 := by
  rw [weierstrassLaurentCoeff, if_neg (by omega), L.G_eq_zero_of_odd _ ⟨i + 1, by ring⟩, mul_zero]

lemma iteratedDeriv_weierstrassPExcept_zero (j : ℕ) :
    iteratedDeriv j ℘[L - (0 : ℂ)] 0 = j ! * weierstrassLaurentCoeff L j := by
  rw [L.iteratedDeriv_weierstrassPExcept_self 0, weierstrassLaurentCoeff]
  split_ifs with h
  · simp
  · rw [L.sumInvPow_zero, Nat.factorial_succ]
    push_cast
    ring

lemma laurent_ode :
    (fun z ↦ z ^ 2 * (deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) + L.g₂ / 2)) =ᶠ[𝓝 0]
      (fun z ↦ 12 * ℘[L - (0 : ℂ)] z) := by
  have hVo : IsOpen (↑L.lattice \ {(0 : ℂ)})ᶜ := L.isOpen_compl_lattice_sdiff
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp
  have hzL : z ∉ L.lattice := fun h ↦ hz ⟨h, hz0⟩
  have h1 : deriv ℘[L - (0 : ℂ)] =ᶠ[𝓝 z] ℘'[L - (0 : ℂ)] := by
    filter_upwards [hVo.mem_nhds hz] with u hu
    exact L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hu
  rw [h1.deriv_eq]
  have hP'a : DifferentiableAt ℂ ℘'[L - (0 : ℂ)] z :=
    (L.analyticOnNhd_derivWeierstrassPExcept 0 z hz).differentiableAt
  have hq : HasDerivAt (fun u ↦ ℘'[L - (0 : ℂ)] u - 2 / u ^ 3)
      (deriv ℘'[L - (0 : ℂ)] z + 6 / z ^ 4) z :=
    (hP'a.hasDerivAt.sub ((hasDerivAt_const z (2 : ℂ)).div (hasDerivAt_pow 3 z)
      (pow_ne_zero 3 hz0))).congr_deriv (by field_simp; ring)
  have heq : ℘'[L] = fun u ↦ ℘'[L - (0 : ℂ)] u - 2 / u ^ 3 :=
    funext derivWeierstrassP_eq_except_zero
  have hval := deriv_derivWeierstrassP hzL
  rw [heq, hq.deriv, weierstrassP_eq_except_zero z] at hval
  have hd : deriv ℘'[L - (0 : ℂ)] z =
      6 * (℘[L - (0 : ℂ)] z + 1 / z ^ 2) ^ 2 - L.g₂ / 2 - 6 / z ^ 4 := by
    linear_combination hval
  rw [hd]
  field_simp
  ring

lemma choose_two_mul (k : ℕ) : (((k + 2).choose 2 : ℕ) : ℂ) * 2 = (k + 2) * (k + 1) := by
  have : (k + 2).choose 2 * 2 = (k + 2) * (k + 1) := by
    rw [Nat.choose_two_right, show k + 2 - 1 = k + 1 by omega]
    exact Nat.div_mul_cancel (by rw [mul_comm]; exact (Nat.even_mul_succ_self (k + 1)).two_dvd)
  exact_mod_cast this

lemma laurent_ode_coeff (k : ℕ) :
    ((k + 2 : ℂ) * (k + 1)) * (iteratedDeriv (k + 2) ℘[L - (0 : ℂ)] 0 -
      6 * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * iteratedDeriv j ℘[L - (0 : ℂ)] 0 *
        iteratedDeriv (k - j) ℘[L - (0 : ℂ)] 0 + (if k = 0 then L.g₂ / 2 else 0)) =
      12 * iteratedDeriv (k + 2) ℘[L - (0 : ℂ)] 0 := by
  have hP : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 := L.analyticAt_weierstrassPExcept 0
  have hPP : AnalyticAt ℂ (fun z ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0 := hP.mul hP
  have hQ : AnalyticAt ℂ (deriv (deriv ℘[L - (0 : ℂ)])) 0 := hP.deriv.deriv
  have h6 : AnalyticAt ℂ (fun z ↦ 6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z)) 0 :=
    analyticAt_const.mul hPP
  have hA : AnalyticAt ℂ (fun z ↦ deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z)) 0 := hQ.sub h6
  have hW : AnalyticAt ℂ (fun z ↦ deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) + L.g₂ / 2) 0 := hA.add analyticAt_const
  have hsq : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) 0 := by fun_prop
  have e := (laurent_ode (L := L)).iteratedDeriv_eq (k + 2)
  rw [iteratedDeriv_fun_mul hsq.contDiffAt hW.contDiffAt,
    iteratedDeriv_const_mul_field] at e
  rw [Finset.sum_eq_single 2 (fun i _ hi ↦ by rw [iteratedDeriv_fun_pow_zero, if_neg hi]; simp)
    (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h)] at e
  rw [iteratedDeriv_fun_add hA.contDiffAt analyticAt_const.contDiffAt,
    iteratedDeriv_fun_sub hQ.contDiffAt h6.contDiffAt, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul hP.contDiffAt hP.contDiffAt, iteratedDeriv_const,
    ← iteratedDeriv_succ', ← iteratedDeriv_succ', iteratedDeriv_fun_pow_zero,
    show k + 2 - 2 = k by omega] at e
  simp only [if_true, Nat.factorial_two, Nat.cast_ofNat] at e
  rw [← e, ← choose_two_mul k]

lemma sum_range_of_odd_eq_zero {f : ℕ → ℂ} (hf : ∀ i, f (2 * i + 1) = 0) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N + 1), f j = ∑ i ∈ Finset.range (N + 1), f (2 * i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, hf, add_zero, Finset.sum_range_succ (n := N + 1)]
    rw [show 2 * N + 1 + 1 = 2 * (N + 1) by ring]

lemma weierstrassLaurentCoeff_recursion (n : ℕ) :
    (((2 * n + 6 : ℂ) * (2 * n + 5)) - 12) * weierstrassLaurentCoeff L (2 * n + 6) =
      6 * ∑ i : Fin (n + 1), weierstrassLaurentCoeff L (2 * ((i : ℕ) + 1)) * weierstrassLaurentCoeff L (2 * (n + 1 - i)) := by
  have e := laurent_ode_coeff (L := L) (2 * n + 4)
  simp only [iteratedDeriv_weierstrassPExcept_zero] at e
  rw [if_neg (by omega)] at e
  have hsum : ∑ j ∈ Finset.range (2 * n + 4 + 1), ((2 * n + 4).choose j : ℂ) *
      ((j ! : ℂ) * weierstrassLaurentCoeff L j) * (((2 * n + 4 - j) ! : ℂ) * weierstrassLaurentCoeff L (2 * n + 4 - j)) =
      ((2 * n + 4) ! : ℂ) * ∑ j ∈ Finset.range (2 * n + 4 + 1),
        weierstrassLaurentCoeff L j * weierstrassLaurentCoeff L (2 * n + 4 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j ≤ 2 * n + 4 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have := Nat.choose_mul_factorial_mul_factorial hj'
    have h' : ((2 * n + 4).choose j : ℂ) * j ! * (2 * n + 4 - j) ! = (2 * n + 4) ! := by
      exact_mod_cast this
    rw [← h']
    ring
  have heven : ∑ j ∈ Finset.range (2 * n + 4 + 1), weierstrassLaurentCoeff L j * weierstrassLaurentCoeff L (2 * n + 4 - j) =
      ∑ i : Fin (n + 1), weierstrassLaurentCoeff L (2 * ((i : ℕ) + 1)) * weierstrassLaurentCoeff L (2 * (n + 1 - i)) := by
    rw [show 2 * n + 4 + 1 = 2 * (n + 2) + 1 by ring,
      sum_range_of_odd_eq_zero (f := fun j ↦ weierstrassLaurentCoeff L j * weierstrassLaurentCoeff L (2 * n + 4 - j))
        (fun i ↦ by simp only [weierstrassLaurentCoeff_odd, zero_mul]),
      Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [show weierstrassLaurentCoeff L (2 * 0) = 0 by simp [weierstrassLaurentCoeff], zero_mul, add_zero,
      show 2 * n + 4 - 2 * (n + 1 + 1) = 0 by omega, show weierstrassLaurentCoeff L 0 = 0 by simp [weierstrassLaurentCoeff],
      mul_zero]
    rw [← Finset.sum_range (fun i ↦ weierstrassLaurentCoeff L (2 * (i + 1)) * weierstrassLaurentCoeff L (2 * (n + 1 - i)))]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have : i < n + 1 := Finset.mem_range.1 hi
    rw [show 2 * n + 4 - 2 * (i + 1) = 2 * (n + 1 - i) by omega]
  rw [hsum, heven] at e
  have hf : ((2 * n + 4) ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfac : (((2 * n + 4 + 2) ! : ℕ) : ℂ) = (2 * n + 6) * (2 * n + 5) * (2 * n + 4) ! := by
    rw [show 2 * n + 4 + 2 = (2 * n + 4 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac, show 2 * n + 4 + 2 = 2 * n + 6 by omega] at e
  push_cast at e
  have hK : ((2 * n + 6 : ℂ) * (2 * n + 5)) ≠ 0 := by
    have : ((2 * n + 6) * (2 * n + 5) : ℕ) ≠ 0 := by positivity
    exact_mod_cast this
  apply mul_left_cancel₀ (mul_ne_zero hK hf)
  linear_combination e

theorem hasSum_weierstrassP_laurent {z : ℂ} (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖) :
    HasSum (fun j ↦ weierstrassLaurentCoeff L j * z ^ j) (℘[L] z - 1 / z ^ 2) := by
  have h := L.weierstrassPExceptSeries_hasSum 0 z 0 (fun l hl ↦ by simpa using hz l hl)
  rw [weierstrassP_eq_except_zero z, add_sub_cancel_right]
  convert h using 2 with j
  rw [sub_zero, PeriodPair.weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars,
    weierstrassLaurentCoeff]
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · simp [hj, L.lattice.zero_mem, L.sumInvPow_zero]

lemma weierstrassLaurentCoeff_two_mul {n : ℕ} (hn : n ≠ 0) :
    weierstrassLaurentCoeff L (2 * n) = (2 * n + 1) * L.G (2 * n + 2) := by
  rw [weierstrassLaurentCoeff, if_neg (by omega)]
  push_cast
  ring

theorem weierstrassLaurentCoeff_eq (n : ℕ) (hn : n ≠ 0) :
    weierstrassLaurentCoeff L (2 * n) = weierstrassCoeff L.g₂ L.g₃ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih, hn with
    | 1, _, _ =>
      rw [weierstrassLaurentCoeff_two_mul one_ne_zero, weierstrassCoeff_one, Rat.smul_def,
        PeriodPair.g₂]
      push_cast
      ring
    | 2, _, _ =>
      rw [weierstrassLaurentCoeff_two_mul two_ne_zero, weierstrassCoeff_two, Rat.smul_def,
        PeriodPair.g₃]
      push_cast
      ring
    | n + 3, ih, _ =>
      have hrec := weierstrassLaurentCoeff_recursion (L := L) n
      have hsum : ∑ i : Fin (n + 1), weierstrassLaurentCoeff L (2 * ((i : ℕ) + 1)) *
          weierstrassLaurentCoeff L (2 * (n + 1 - i)) = ∑ i : Fin (n + 1),
            weierstrassCoeff L.g₂ L.g₃ ((i : ℕ) + 1) * weierstrassCoeff L.g₂ L.g₃ (n + 1 - i) :=
        Finset.sum_congr rfl fun i _ ↦ by
          have := i.isLt
          rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      rw [hsum] at hrec
      rw [weierstrassCoeff_add_three, Rat.smul_def, show 2 * (n + 3) = 2 * n + 6 by ring]
      have hK : ((2 * n + 6 : ℂ) * (2 * n + 5) - 12) ≠ 0 := by
        have : ((2 * n + 6 : ℂ) * (2 * n + 5) - 12) = 2 * (2 * n + 9) * (n + 1) := by ring
        rw [this]
        have : ((2 * (2 * n + 9) * (n + 1) : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.2 (by positivity)
        exact_mod_cast this
      apply mul_left_cancel₀ hK
      rw [hrec]
      have h1 : (2 * ((n : ℂ) + 3) + 3) ≠ 0 := by
        have : ((2 * (n + 3) + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        exact_mod_cast this
      have h2 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      push_cast
      field_simp
      ring

theorem mul_G_eq_weierstrassCoeff {n : ℕ} (hn : n ≠ 0) :
    (2 * n + 1) * L.G (2 * n + 2) = weierstrassCoeff L.g₂ L.g₃ n := by
  rw [← weierstrassLaurentCoeff_two_mul hn, weierstrassLaurentCoeff_eq n hn]

theorem G_eq_weierstrassCoeff_div {n : ℕ} (hn : n ≠ 0) :
    L.G (2 * n + 2) = weierstrassCoeff L.g₂ L.g₃ n / (2 * n + 1) := by
  have h : (2 * (n : ℂ) + 1) ≠ 0 := by
    have : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact_mod_cast this
  rw [← mul_G_eq_weierstrassCoeff hn, mul_div_cancel_left₀ _ h]

theorem G_eq_aeval_eisensteinPoly {n : ℕ} (hn : n ≠ 0) :
    L.G (2 * n + 2) = MvPolynomial.aeval ![L.g₂, L.g₃] (eisensteinPoly n) := by
  rw [aeval_eisensteinPoly, G_eq_weierstrassCoeff_div hn]
  rfl

theorem exists_G_eq_aeval {k : ℕ} (hk : 2 ≤ k) :
    ∃ P : MvPolynomial (Fin 2) ℚ, ∀ L : PeriodPair,
      L.G (2 * k) = MvPolynomial.aeval ![L.g₂, L.g₃] P := by
  refine ⟨eisensteinPoly (k - 1), fun L ↦ ?_⟩
  rw [show 2 * k = 2 * (k - 1) + 2 by omega]
  exact G_eq_aeval_eisensteinPoly (by omega)

theorem G_eq_of_g₂_g₃ {L' : PeriodPair} {t : ℂ} (h₂ : L'.g₂ = t ^ 4 * L.g₂)
    (h₃ : L'.g₃ = t ^ 6 * L.g₃) {k : ℕ} (hk : 2 ≤ k) :
    L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, G_eq_weierstrassCoeff_div hn,
    G_eq_weierstrassCoeff_div hn, h₂, h₃, weierstrassCoeff_scale]
  ring

end Elliptic
end GroundTheory.Global
