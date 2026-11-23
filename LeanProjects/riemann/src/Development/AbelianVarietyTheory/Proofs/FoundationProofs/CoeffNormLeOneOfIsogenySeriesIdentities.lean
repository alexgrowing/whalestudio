import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralSeriesOfCommonDivisorLineProductsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneFunctionalEquationPadicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplexStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLawsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Isog

theorem coeff_lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) (n : ℕ) :
    PowerSeries.coeff n (lineSer e x) = PowerSeries.coeff n e - if n = 2 then x else 0 := by
  simp [lineSer, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

theorem constantCoeff_lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) :
    PowerSeries.constantCoeff (lineSer e x) = PowerSeries.constantCoeff e := by
  simp [lineSer]

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_le_max' (a b : ℂ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_coeff_lineSer_le {e : PowerSeries ℂ_[p]} (he : IntSer e) (x : ℂ_[p]) (n : ℕ) :
    ‖PowerSeries.coeff n (lineSer e x)‖ ≤ max 1 ‖x‖ := by
  rw [coeff_lineSer]
  refine (norm_sub_le_max' _ _).trans (max_le_max (he n) ?_)
  split_ifs <;> simp

theorem exists_norm_coeff_lineSer {e : PowerSeries ℂ_[p]} (he : IntSer e)
    (he0 : PowerSeries.constantCoeff e = 1) (x : ℂ_[p]) :
    ∃ n, max 1 ‖x‖ ≤ ‖PowerSeries.coeff n (lineSer e x)‖ := by
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · refine ⟨0, ?_⟩
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lineSer, he0, norm_one]
    exact max_le le_rfl hx
  · refine ⟨2, ?_⟩
    rw [max_eq_right hx.le]
    have h1 := norm_sub_le_max' (PowerSeries.coeff 2 e) (PowerSeries.coeff 2 (lineSer e x))
    have h2 : PowerSeries.coeff 2 e - PowerSeries.coeff 2 (lineSer e x) = x := by
      rw [coeff_lineSer]; simp
    rw [h2] at h1
    rcases le_max_iff.1 h1 with h | h
    · exact absurd (h.trans (he 2)) (not_le.2 hx)
    · exact h

theorem IntSer.bdd {f : PowerSeries ℂ_[p]} (hf : IntSer f) : BddSer f := ⟨1, hf⟩

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp

theorem bdd_prod {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℂ_[p]) (hg : ∀ i, BddSer (g i)) :
    BddSer (∏ i ∈ s, g i) :=
  Finset.prod_induction g BddSer (fun a b ha hb => ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 a b ha hb).2.2)
    (IntSer.bdd intSer_one) (fun i _ => hg i)

theorem int_pow {g : PowerSeries ℂ_[p]} (hg : IntSer g) (k : ℕ) : IntSer (g ^ k) := by
  induction k with
  | zero => simpa using intSer_one
  | succ k ih => rw [pow_succ]; exact ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).1 _ _ ih hg).2.2

theorem subst_lineSer_sub {e h : PowerSeries ℂ_[p]} (h0 : PowerSeries.constantCoeff h = 0)
    (x₀ x₁ : ℂ_[p]) :
    (PowerSeries.subst h (lineSer e x₀) : PowerSeries ℂ_[p]) - PowerSeries.subst h (lineSer e x₁) =
      PowerSeries.C (x₁ - x₀) * h ^ 2 := by
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have e1 : lineSer e x₀ = lineSer e x₁ + (x₁ - x₀) • PowerSeries.X ^ 2 := by
    rw [PowerSeries.smul_eq_C_mul]
    simp only [lineSer, map_sub]; ring
  rw [e1, PowerSeries.subst_add hs, PowerSeries.subst_smul hs, PowerSeries.subst_pow hs,
    PowerSeries.subst_X hs, PowerSeries.smul_eq_C_mul]
  ring

theorem bdd_of_mul_sq {Ψ h : PowerSeries ℂ_[p]} {c : ℂ_[p]} (hc : c ≠ 0) (hh : IntSer h)
    (h0 : PowerSeries.constantCoeff h = 0) (h1 : ‖PowerSeries.coeff 1 h‖ = 1)
    (hb : BddSer (Ψ * (PowerSeries.C c * h ^ 2))) : BddSer Ψ := by
  obtain ⟨h', rfl⟩ := PowerSeries.X_dvd_iff.2 h0
  have hi : IntSer h' := fun n => by simpa using hh (n + 1)
  have hc0 : ‖PowerSeries.constantCoeff h'‖ = 1 := by
    have := PowerSeries.coeff_succ_X_mul 0 h'
    simp only [zero_add] at this
    rw [this] at h1
    simpa using h1
  have hne : PowerSeries.constantCoeff h' ≠ 0 := by
    intro h; rw [h] at hc0; simp at hc0
  have hinv := (GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.2.2.1 h' hi hc0
  have hb2 := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ hb (((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 c⁻¹).1
    (IntSer.bdd (int_pow hinv 2))).2.2)).2.2
  have hm := PowerSeries.mul_inv_cancel h' hne
  have hcc : (PowerSeries.C c : PowerSeries ℂ_[p]) * PowerSeries.C c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have e : Ψ * (PowerSeries.C c * (PowerSeries.X * h') ^ 2) * (PowerSeries.C c⁻¹ * h'⁻¹ ^ 2) =
      Ψ * PowerSeries.X ^ 2 := by
    calc _ = Ψ * PowerSeries.X ^ 2 * (PowerSeries.C c * PowerSeries.C c⁻¹) * (h' * h'⁻¹) ^ 2 := by ring
      _ = _ := by rw [hm, hcc]; ring
  rw [e] at hb2
  obtain ⟨B, hB⟩ := hb2
  exact ⟨B, fun n => by simpa [PowerSeries.coeff_mul_X_pow] using hB (n + 2)⟩

end GlobalTheory.EvenTheta.Isog

namespace GlobalTheory.EvenTheta
open Isog

theorem intSer_of_isogeny_identities : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (e h S f : PowerSeries ℂ_[p]) (x₀ x₁ : ℂ_[p]) (y : Fin k → ℂ_[p]) (y' : Fin (2 * k) → ℂ_[p]), IntSer e → PowerSeries.constantCoeff e = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖((2 * k : ℕ) : ℂ_[p])‖ < 1 → PowerSeries.constantCoeff S = 1 → PowerSeries.constantCoeff f = 1 → f ^ 2 = S * lineSer e x₀ → (PowerSeries.subst h f : PowerSeries ℂ_[p]) = S ^ k * ∏ i, lineSer e (y i) → (PowerSeries.subst h (S * lineSer e x₁) : PowerSeries ℂ_[p]) = S ^ (2 * k) * ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → (∃ j, y' j = x₀) → (∃ j, y' j = x₁) → x₀ ≠ x₁ → IntSer f ∧ ‖x₀‖ ≤ 1 := by
  intro p _ k e h S f x₀ x₁ y y' he he0 hh h0 h1 hk hS0 hf0 hf2 hf hS hy ⟨j₀, hj₀⟩ ⟨j₁, hj₁⟩ hx
  obtain ⟨rI, rB, rC, -, -, rS, rM⟩ := GlobalTheory.T.padicComplex_integral_bounded_series_laws p
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hG : ∀ x, BddSer (lineSer e x) := fun x => ⟨_, norm_coeff_lineSer_le he x⟩
  have hG0 : ∀ x, PowerSeries.constantCoeff (lineSer e x) = 1 := fun x => by
    rw [constantCoeff_lineSer, he0]
  have hGs : ∀ x n, ‖PowerSeries.coeff n (PowerSeries.subst h (lineSer e x) : PowerSeries ℂ_[p])‖ ≤
      max 1 ‖x‖ := fun x => rS _ h _ (norm_coeff_lineSer_le he x) hh h0
  set P := ∏ i, lineSer e (y i) with hP
  set P' := ∏ j, lineSer e (y' j) with hP'
  have hPb : BddSer P := bdd_prod _ _ fun i => hG _
  have hP'b : BddSer P' := bdd_prod _ _ fun i => hG _
  have hP0 : PowerSeries.constantCoeff P = 1 := by simp [hP, map_prod, hG0]
  have hP'0 : PowerSeries.constantCoeff P' = 1 := by simp [hP', map_prod, hG0]
  have hinv := PowerSeries.mul_inv_cancel (S ^ (2 * k)) (by simp [hS0])
  set Ψ : PowerSeries ℂ_[p] := PowerSeries.subst h S * (S ^ (2 * k))⁻¹ with hΨ
  set A : PowerSeries ℂ_[p] := PowerSeries.subst h (lineSer e x₀) with hA
  set B : PowerSeries ℂ_[p] := PowerSeries.subst h (lineSer e x₁) with hB
  have eA : Ψ * A = P ^ 2 := by
    have h2 : (PowerSeries.subst h S : PowerSeries ℂ_[p]) * A = S ^ (2 * k) * P ^ 2 := by
      rw [hA, ← PowerSeries.subst_mul hs, ← hf2, PowerSeries.subst_pow hs, hf]; ring
    rw [hΨ]
    linear_combination (S ^ (2 * k))⁻¹ * h2 + P ^ 2 * hinv
  have eB : Ψ * B = P' := by
    rw [PowerSeries.subst_mul hs] at hS
    rw [hΨ]
    linear_combination (S ^ (2 * k))⁻¹ * hS + P' * hinv
  have eAB : A - B = PowerSeries.C (x₁ - x₀) * h ^ 2 := subst_lineSer_sub h0 x₀ x₁
  have hB0 : PowerSeries.constantCoeff B = 1 := by
    have e1 : lineSer e x₁ = 1 + PowerSeries.X * PowerSeries.mk fun n =>
        PowerSeries.coeff (n + 1) (lineSer e x₁) := by
      conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (lineSer e x₁)]
      rw [hG0, map_one, add_comm]
    have e2 : (PowerSeries.subst h (1 : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p]) = 1 := by
      rw [← PowerSeries.coe_substAlgHom hs, map_one]
    rw [hB, e1, PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, e2]
    simp [h0]
  have hΨ0 : PowerSeries.constantCoeff Ψ = 1 := by
    have := congrArg PowerSeries.constantCoeff eB
    rwa [map_mul, hB0, hP'0, mul_one] at this
  have hΨb : BddSer Ψ := by
    refine bdd_of_mul_sq (sub_ne_zero.2 hx.symm) hh h0 h1 ?_
    rw [← eAB, mul_sub, eA, eB, sq]
    exact (rB _ _ (rB _ _ hPb hPb).2.2 hP'b).2.1
  have hΨi : IntSer Ψ :=
    GlobalTheory.T.integral_series_of_common_divisor_line_products p k (2 * k) e Ψ A B y y' (IntSer.bdd he) hΨb ⟨_, hGs x₀⟩ ⟨_, hGs x₁⟩ hΨ0 eA eB hy
  have hP'm : ∀ n, ‖PowerSeries.coeff n P'‖ ≤ max 1 ‖x₁‖ := fun n => by
    have := rM Ψ B _ _ hΨi (hGs x₁) n
    rwa [eB, one_mul] at this
  have hj : j₀ ≠ j₁ := by
    rintro rfl
    exact hx (hj₀.symm.trans hj₁)
  set R := ∏ j ∈ (Finset.univ.erase j₁).erase j₀, lineSer e (y' j) with hR
  have hRb : BddSer R := bdd_prod _ _ fun i => hG _
  have hR0 : PowerSeries.constantCoeff R = 1 := by simp [hR, map_prod, hG0]
  have eP' : P' = lineSer e x₁ * (lineSer e x₀ * R) := by
    rw [hP', hR, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₁),
      ← Finset.mul_prod_erase (Finset.univ.erase j₁) _ (a := j₀) (by simp [hj]), hj₀, hj₁]
  have hGR : IntSer (lineSer e x₀ * R) := fun n => by
    obtain ⟨i, hi⟩ := exists_norm_coeff_lineSer he he0 x₁
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ (hG x₁) (rB _ _ (hG x₀) hRb).2.2 (eP' ▸ hP'm) i n
    have hpos : (0 : ℝ) < max 1 ‖x₁‖ := lt_max_of_lt_left one_pos
    have h4 := mul_le_mul_of_nonneg_right hi
      (norm_nonneg (PowerSeries.coeff n (lineSer e x₀ * R)))
    exact le_of_mul_le_mul_left (by rw [mul_one]; exact h4.trans h3) hpos
  have hGi : IntSer (lineSer e x₀) := fun n => by
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ (hG x₀) hRb hGR n 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0, norm_one, mul_one] at h3
  have hx0 : ‖x₀‖ ≤ 1 := by
    obtain ⟨i, hi⟩ := exists_norm_coeff_lineSer he he0 x₀
    exact (le_max_right _ _).trans (hi.trans (hGi i))
  have hPi : IntSer P := fun n => by
    have hAi : IntSer A := rS _ h _ hGi hh h0
    have h2 : IntSer (P * P) := by
      rw [← sq, ← eA]; exact (rI _ _ hΨi hAi).2.2
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ hPb hPb h2 n 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0, norm_one, mul_one] at h3
  refine ⟨GlobalTheory.T.powerSeriesCoeffNormLeOne_functional_equation_padic p f h (lineSer e x₀ ^ k) P (2 * k) hf0 hh h0 h1 hk (int_pow hGi k)
    (by simp [hG0]) hPi hP0 ?_, hx0⟩
  rw [hf, pow_mul, hf2]; ring

end GlobalTheory.EvenTheta
