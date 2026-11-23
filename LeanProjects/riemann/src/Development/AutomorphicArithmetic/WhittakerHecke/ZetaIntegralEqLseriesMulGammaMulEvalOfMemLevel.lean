import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleAbsRealIdeleNatIdeleUnitIdeles
import Development.AutomorphicArithmetic.WhittakerHecke.HasSumCoprimeIntegralEqIdeleIntegral
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsIdeleCorrectingLowerRightEntry
import Development.AutomorphicArithmetic.WhittakerHecke.BottomRowCongruenceIffIdeleCongruence
import Development.AutomorphicArithmetic.WhittakerHecke.IdeleCongruenceConditionMulCongruenceUnitIff
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralEvenPowerGaussianMulAbsRpow
import Development.AutomorphicArithmetic.WhittakerHecke.HasSumCoprimeInvPowTwoMulEqLSeries
import Development.AutomorphicArithmetic.WhittakerHecke.IdeleCongruenceArchIdeleMulFiniteNatIdele
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsArchIdeleNatIdeleCongruenceUnitFactorizati
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem re_mul' (a b : A ℚ) : re (a * b) = re a * re b := by simp [re, map_mul]

private theorem re_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : re (t : A ℚ) = 1 := by
  have h : TR.pInf ℚ (t : A ℚ) = 1 := by
    show (TR.infEq ℚ).symm (t : A ℚ).1 = 1
    rw [ht.1, map_one]
  simp [re, h]

private theorem ab_mul' (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by simp [ab, map_mul]

private theorem homog {p : MvPolynomial (Fin 2) ℂ} {d : ℕ} (hp : p.IsHomogeneous d) (c a b : ℂ) :
    MvPolynomial.eval ![c * a, c * b] p = c ^ d * MvPolynomial.eval ![a, b] p := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m 0 + m 1 = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow, ← hdeg, pow_add]
  ring

private theorem cpow_split (r : ℝ) (hr : r ≠ 0) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (((|r| * (n : ℝ)⁻¹ : ℝ)) : ℂ) ^ (2 * s) / ((|r| : ℝ) : ℂ) =
      ((n : ℂ) ^ (-(2 * s))) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) := by
  have hr' : (((|r| : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hr
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg r) (by positivity) (2 * s),
    Complex.cpow_sub _ _ hr', Complex.cpow_one, Complex.cpow_neg, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne)]
  ring

theorem UpperTheory.zeta_integral_eq_lseries_mul_gamma_mul_eval_of_mem_level :
    ∀ (N : ℕ), 0 < N → ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) → ∀ s : ℂ, 4 < s.re → ∀ k ∈ KK ℚ, k ∈ SS N →
        ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        Zr N p s k = (cT N : ℂ) * LSeries (sqN N) s * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e)) *
          MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p := by
  intro N hN e p hp s hs k hK hS t hsin hcos
  obtain ⟨ζ, hζU, hζ⟩ := UpperTheory.exists_idele_correcting_lowerRight_entry N hN k hK hS
  have hs0 : 0 < s.re := by linarith
  have hs1 : 1 < s.re := by linarith
  set ρ : ℂ := MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p with hρ
  let f0 : IdeleGroup ℚ → ℂ := fun z => (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)
  let f : IdeleGroup ℚ → ℂ := fun y => f0 (y * ζ)
  have hshift : Zr N p s k = ∫ y, f y ∂(ideleMeasure ℚ) := (integral_mul_right_eq_self f0 ζ).symm
  have habU : ∀ τ ∈ UU, ∀ y : (A ℚ)ˣ, ab (y * τ) = ab y := fun τ hτ y => by
    rw [ab_mul', (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).2.2.1 τ hτ, mul_one]
  have hreU : ∀ τ : (A ℚ)ˣ, τ ∈ UU → ∀ y : (A ℚ)ˣ, re ((y * τ : (A ℚ)ˣ) : A ℚ) = re (y : A ℚ) := fun τ hτ y => by
    rw [Units.val_mul, re_mul', re_UU hτ, mul_one]
  have hf : ∀ y : (A ℚ)ˣ, f y = if ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) then
      ((re (y : A ℚ) : ℝ) : ℂ) ^ (2 * e) * ρ * Complex.exp (-(Real.pi : ℂ) * ((re (y : A ℚ) ^ 2 : ℝ) : ℂ)) * ((ab y : ℝ) : ℂ) ^ (2 * s) else 0 := by
    intro y
    have hre : ∀ j, re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k j) = re (y : A ℚ) * re (k 1 j) := fun j => by
      rw [re_mul', hreU ζ hζU y]; rfl
    have hc := UpperTheory.bottomRow_congruence_iff_idele_congruence N hN k hK hS ζ hζU hζ y
    have hfun : (fun i => ((re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k i) : ℝ) : ℂ)) =
        ![((re (y : A ℚ) : ℝ) : ℂ) * (Real.sin t : ℂ), ((re (y : A ℚ) : ℝ) : ℂ) * (Real.cos t : ℂ)] := by
      funext i
      fin_cases i
      · show ((re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) : ℝ) : ℂ) = ((re (y : A ℚ) : ℝ) : ℂ) * (Real.sin t : ℂ)
        rw [hre, hsin, Complex.ofReal_mul]
      · show ((re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1) : ℝ) : ℂ) = ((re (y : A ℚ) : ℝ) : ℂ) * (Real.cos t : ℂ)
        rw [hre, hcos, Complex.ofReal_mul]
    have hsq : re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) ^ 2 + re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1) ^ 2 = re (y : A ℚ) ^ 2 := by
      rw [hre, hre, hsin, hcos]
      have := Real.sin_sq_add_cos_sq t
      calc _ = re (y : A ℚ) ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
        _ = _ := by rw [this, mul_one]
    show (PhiN N p fun j => ((y * ζ : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab (y * ζ) : ℝ) : ℂ) ^ (2 * s) = _
    rw [habU ζ hζU y]
    by_cases hq : ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1)
    · have hq' : ∀ v, Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) ∧ Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) := by
        exact hc.mpr hq
      rw [if_pos hq, PhiN, if_pos hq', hfun, homog hp, hsq]
    · have hq' : ¬ ∀ v, Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) ∧ Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) := by
        intro h
        exact hq (hc.mp h)
      rw [if_neg hq, PhiN, if_neg hq', zero_mul]
  have hinv : ∀ τ ∈ TT N, ∀ y : IdeleGroup ℚ, f (y * τ) = f y := by
    intro τ hτ y
    rw [hf, hf, hreU τ hτ.1 y, habU τ hτ.1 y]
    simp only [UpperTheory.ideleCongruenceCondition_mul_congruenceUnit_iff N hN τ hτ y]
  have hsupp : ∀ y : IdeleGroup ℚ, f y ≠ 0 → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT N ∧ y = iy r * pin n * τ := by
    intro y hy
    refine UpperTheory.exists_archIdele_natIdele_congruenceUnit_factorization N hN y ?_
    by_contra h
    exact hy (by rw [hf, if_neg h])
  let J : ℝ → ℂ := fun r => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)
  have hJ := UpperTheory.integral_even_power_gaussian_mul_abs_rpow e s hs0
  have hval : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∀ r : ℝ, r ≠ 0 →
      f (iy r * pin n) / ((|r| : ℝ) : ℂ) = (ρ * ((n : ℕ) : ℂ) ^ (-(2 * s))) * J r := by
    intro n r hr
    have hab : ab (iy r * pin n) = |r| * ((n : ℕ) : ℝ)⁻¹ := by
      rw [ab_mul', (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).1 r hr, (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).2.1 n n.2.1]
    rw [hf, if_pos (UpperTheory.ideleCongruence_archIdele_mul_finiteNatIdele N hN n r n.2.1 n.2.2 hr), (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).2.2.2 r n hr n.2.1, hab, mul_div_assoc,
      cpow_split r hr n n.2.1 s]
    simp only [J]
    ring
  have hae : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, (fun r : ℝ => f (iy r * pin n) / ((|r| : ℝ) : ℂ)) =ᵐ[volume]
      fun r => (ρ * ((n : ℕ) : ℂ) ^ (-(2 * s))) * J r := by
    intro n
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with r hr
    exact hval n r hr
  have hint : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, Integrable (fun r : ℝ => f (iy r * pin n) / ((|r| : ℝ) : ℂ)) :=
    fun n => (hJ.1.const_mul _).congr (hae n).symm
  have hS0 := UpperTheory.hasSum_coprime_inv_pow_two_mul_eq_LSeries N s hN hs1
  have hnorm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖ =
      ‖ρ‖ * ‖((n : ℕ) : ℂ) ^ (-(2 * s))‖ * ∫ r : ℝ, ‖J r‖ := by
    intro n
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae n] with r hr
    rw [hr, norm_mul, norm_mul]
  have hsm : Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖) := by
    simp only [hnorm]
    exact (hS0.summable.norm.mul_left ‖ρ‖).mul_right _
  have hmain := (UpperTheory.hasSum_coprime_integral_eq_idele_integral) N N hN f hinv hsupp hint hsm
  have hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, (cT N : ℂ) * ∫ r : ℝ, f (iy r * pin n) / ((|r| : ℝ) : ℂ) =
      ((cT N : ℂ) * ρ * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e))) * ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    intro n
    rw [integral_congr_ae (hae n), integral_const_mul, hJ.2]
    ring
  simp only [hterm] at hmain
  rw [hshift, hmain.unique (hS0.mul_left _)]
  ring
