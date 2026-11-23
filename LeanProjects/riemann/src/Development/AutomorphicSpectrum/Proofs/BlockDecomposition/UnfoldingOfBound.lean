import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailBis

open Ad3 Ad3.S
open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegralWeight

lemma exp_split (c x y : ℝ) :
    cexp (2 * π * I * c * ((x : ℂ) + y * I)) =
      cexp (((2 * π * c * x : ℝ) : ℂ) * I) * (Real.exp (-(2 * π * c * y)) : ℂ) := by
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  have h : I * I = -1 := I_mul_I
  linear_combination (2 * π * c * y : ℂ) * h

lemma norm_exp_height (c x y : ℝ) :
    ‖cexp (2 * π * I * c * ((x : ℂ) + y * I))‖ = Real.exp (-(2 * π * c * y)) := by
  rw [exp_split, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma integral_exp_int (j : ℤ) :
    ∫ x : ℝ in (0 : ℝ)..1, cexp (2 * π * I * j * x) = if j = 0 then 1 else 0 :=
  _root_.UpperTheory.Reformulated.B.Yra2.main j

lemma coeff_integral (F : ℝ → ℂ) (a : ℕ → ℂ) (y : ℝ)
    (hs : ∀ x : ℝ, HasSum (fun m : ℕ => a m * cexp (2 * π * I * m * ((x : ℂ) + y * I))) (F x))
    (hsum : Summable fun m : ℕ => ‖a m‖ * Real.exp (-(2 * π * m * y))) (q : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, F x * cexp (-(2 * π * I * q * x)) =
      a q * (Real.exp (-(2 * π * q * y)) : ℂ) := by
  have key : HasSum (fun m : ℕ => ∫ x : ℝ in (0 : ℝ)..1,
      a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) * cexp (-(2 * π * I * q * x)))
      (∫ x : ℝ in (0 : ℝ)..1, F x * cexp (-(2 * π * I * q * x))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => ‖a m‖ * Real.exp (-(2 * π * m * y))) ?_ ?_ ?_ ?_ ?_
    · intro m
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · intro m
      refine Eventually.of_forall fun x _ => ?_
      have h2 : ‖cexp (-(2 * π * I * q * x))‖ = 1 := by
        have : -(2 * π * I * q * x) = (((-(2 * π * q * x)) : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, norm_exp_ofReal_mul_I]
      have h3 := norm_exp_height (m : ℝ) x y
      push_cast at h3
      rw [norm_mul, norm_mul, h2, h3, mul_one]
    · exact Eventually.of_forall fun x _ => hsum
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun x _ => ?_
      exact (hs x).mul_right _
  have hval : ∀ m : ℕ, (∫ x : ℝ in (0 : ℝ)..1,
      a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) * cexp (-(2 * π * I * q * x))) =
      if m = q then a q * (Real.exp (-(2 * π * q * y)) : ℂ) else 0 := by
    intro m
    have hfun : (fun x : ℝ => a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) *
        cexp (-(2 * π * I * q * x))) = fun x : ℝ =>
        (a m * (Real.exp (-(2 * π * m * y)) : ℂ)) *
          cexp (2 * π * I * (((m : ℤ) - (q : ℤ) : ℤ) : ℂ) * x) := by
      funext x
      have h3 := exp_split (m : ℝ) x y
      rw [ofReal_natCast] at h3
      have h4 : cexp (2 * π * I * (((m : ℤ) - (q : ℤ) : ℤ) : ℂ) * x) =
          cexp (((2 * π * m * x : ℝ) : ℂ) * I) * cexp (-(2 * π * I * q * x)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [h3, h4]; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_int]
    by_cases h : m = q
    · subst h; simp
    · have : ((m : ℤ) - (q : ℤ)) ≠ 0 := by omega
      simp [h, this]
  simp_rw [hval] at key
  exact key.unique (hasSum_ite_eq q _)

lemma conj_inv_apply {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (u : ZMod M) :
    conj (ψ⁻¹ u) = ψ u := by
  have h := MulChar.star_apply' ψ⁻¹ u
  simpa using h

theorem unfolding_of_bound : B2 → HorizontalIntegralTwisted := by
  intro hB k N M ν _ _ hM χ f a hf ψ hν hψ y hy
  have : Fact (1 < M) := ⟨hM⟩
  have hz : ∀ x : ℝ, 0 < ((x : ℂ) + y * I).im := fun x => by simpa using hy
  let z : ℝ → UpperHalfPlane := fun x => ⟨(x : ℂ) + y * I, hz x⟩
  let F : ℝ → ℂ := fun x => f (z x)
  let P : ℤ → ℂ := fun n => ψ⁻¹ (n : ZMod M)
  have hψ0 : ∀ φ : DirichletCharacter ℂ M, φ 0 = 0 := fun φ =>
    MulChar.map_nonunit φ not_isUnit_zero
  have hP0 : P 0 = 0 := by simp [P, hψ0]
  have hP1 : ∀ n, ‖P n‖ ≤ 1 := fun n => DirichletCharacter.norm_le_one _ _
  obtain ⟨-, -, hsum, -⟩ := hB P ν hν hP0 hP1
  have hs : ∀ x : ℝ, HasSum (fun m : ℕ => a m * cexp (2 * π * I * m * ((x : ℂ) + y * I))) (F x) :=
    fun x => hf.exp (z x)
  have hnA : ∀ (m : ℕ) (x : ℝ), ‖a m * cexp (2 * π * I * m * ((x : ℂ) + y * I))‖ =
      ‖a m‖ * Real.exp (-(2 * π * m * y)) := by
    intro m x
    have h3 := norm_exp_height (m : ℝ) x y
    push_cast at h3
    rw [norm_mul, h3]
  have hsumA : Summable fun m : ℕ => ‖a m‖ * Real.exp (-(2 * π * m * y)) := by
    have := summable_norm_iff.mpr (hs 0).summable
    simpa only [hnA] using this
  have hFc : Continuous F := by
    have : F = fun x : ℝ => ∑' m : ℕ, a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) :=
      funext fun x => (hs x).tsum_eq.symm
    rw [this]
    exact continuous_tsum (fun m => by fun_prop) hsumA (fun m x => (hnA m x).le)
  have hC : ∀ x, ‖F x‖ ≤ ∑' m : ℕ, ‖a m‖ * Real.exp (-(2 * π * m * y)) := fun x =>
    (hs x).norm_le_of_bounded hsumA.hasSum (fun m => (hnA m x).le)
  set C := ∑' m : ℕ, ‖a m‖ * Real.exp (-(2 * π * m * y)) with hCdef
  let t : ℤ → ℝ → ℂ := fun n x => P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * ((x : ℂ) + y * I))
  have htc : ∀ n, Continuous (t n) := fun n => by
    simp only [t, ee]; fun_prop
  have hee : ∀ (n : ℤ) (x : ℝ), ee ((n : ℂ) ^ 2 * ((x : ℂ) + y * I)) =
      cexp (((2 * π * ((n : ℝ) ^ 2) * x : ℝ) : ℂ) * I) * (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ) := by
    intro n x
    rw [← exp_split, ee]; congr 1; push_cast; ring
  have hnt : ∀ n x, ‖t n x‖ = ‖t n 0‖ := by
    intro n x
    simp only [t, norm_mul, hee, norm_exp_ofReal_mul_I]
  have hsum0 : Summable fun n => ‖t n 0‖ := hsum (z 0)
  have hHS : ∀ x : ℝ, HasSum (fun n => t n x) (th P ν ((x : ℂ) + y * I)) := fun x =>
    ((hsum (z x)).of_norm).hasSum
  have key : HasSum (fun n : ℤ => ∫ x : ℝ in (0 : ℝ)..1, F x * conj (t n x))
      (∫ x : ℝ in (0 : ℝ)..1, F x * conj (th P ν ((x : ℂ) + y * I))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => C * ‖t n 0‖) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (hFc.mul (continuous_conj.comp (htc n))).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x _ => ?_
      rw [norm_mul, RCLike.norm_conj, hnt n x]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    · exact Eventually.of_forall fun x _ => hsum0.mul_left C
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun x _ => ?_
      exact ((hHS x).map (starRingEnd ℂ) continuous_conj).mul_left (F x)
  let h : ℤ → ℂ := fun n => ψ (n : ZMod M) * (n : ℂ) ^ ν *
    (a (n.natAbs ^ 2) * (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ))
  have hval : ∀ n : ℤ, (∫ x : ℝ in (0 : ℝ)..1, F x * conj (t n x)) = h n := by
    intro n
    have hqZ : ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := by simp
    have hqR : ((n.natAbs ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
      rw [← Int.cast_natCast (R := ℝ), hqZ, Int.cast_pow]
    have hqC : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
      rw [← Int.cast_natCast (R := ℂ), hqZ, Int.cast_pow]
    have hco := coeff_integral F a y hs hsumA (n.natAbs ^ 2)
    rw [hqC, hqR] at hco
    have hfun : (fun x : ℝ => F x * conj (t n x)) = fun x : ℝ =>
        (ψ (n : ZMod M) * (n : ℂ) ^ ν * (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ)) *
          (F x * cexp (-(2 * π * I * (n : ℂ) ^ 2 * x))) := by
      funext x
      have hc : conj (cexp (((2 * π * ((n : ℝ) ^ 2) * x : ℝ) : ℂ) * I)) =
          cexp (-(2 * π * I * (n : ℂ) ^ 2 * x)) := by
        rw [← Complex.exp_conj]; congr 1
        simp only [map_mul, conj_ofReal, conj_I]
        push_cast; ring
      simp only [t, hee, map_mul, map_pow, conj_ofReal, map_intCast, P, conj_inv_apply, hc]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hco]
    simp only [h]
    have hR : (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ) =
        (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ) * (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ) := by
      rw [← ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [hR]; ring
  simp_rw [hval] at key
  have h0 : h 0 = 0 := by simp [h, hψ0]
  have hfold := key.nat_add_neg
  rw [h0, add_zero] at hfold
  convert hfold using 1
  funext n
  have hneg : ψ (-(n : ZMod M)) = (-1) ^ ν * ψ (n : ZMod M) := by
    rw [← hψ, ← map_mul]; congr 1; ring
  have h1 : ((-1 : ℂ) ^ ν) * (-1) ^ ν = 1 := by
    rw [← mul_pow]; simp
  simp only [h, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_natCast, Int.cast_neg, hneg,
    even_two, Even.neg_pow]
  rw [neg_pow (n : ℂ) ν]
  linear_combination (-(ψ (n : ZMod M) * (n : ℂ) ^ ν * a (n ^ 2) *
    (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ))) * h1

end GlobalTheory.CompanionTheory.HalfIntegralWeight
