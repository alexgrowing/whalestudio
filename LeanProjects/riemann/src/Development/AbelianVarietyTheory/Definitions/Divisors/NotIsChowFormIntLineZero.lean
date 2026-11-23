import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

set_option autoImplicit false in
open MvPolynomial NumberField IsDedekindDomain Module Filter in
open scoped ENNReal in

theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

theorem not_isChowFormInt_line_zero {K : Type} [Field K] {δ : ℕ} {g : MvPolynomial (Fin (0 + 1) × Fin 2) K}
    (hf' : IsChowFormInt (⊥ : Ideal (MvPolynomial (Fin 2) K)) 0 δ g) : False := by
  refine hf'.ne_zero ?_
  apply MvPolynomial.map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  refine MvPolynomial.funext fun u => ?_
  rw [map_zero, eval_map, ← aeval_def, hf'.zero_iff]
  by_cases hu : u (0, 0) = 0
  · refine ⟨![1, 0], by simp, fun g hg => by rw [Ideal.mem_bot.1 hg, map_zero], fun i => ?_⟩
    fin_cases i
    simp [Fin.sum_univ_two, hu]
  · refine ⟨![u (0, 1), -u (0, 0)], by simp [hu], fun g hg => by rw [Ideal.mem_bot.1 hg, map_zero], fun i => ?_⟩
    fin_cases i
    simp [Fin.sum_univ_two, mul_comm]

theorem imageDeg_line_zero : imageDeg (stdPoint 2) 0 = 0 := by
  by_contra h
  obtain ⟨N, b, f, hf⟩ := (imageDeg_pos_iff _ 0).1 (Nat.pos_of_ne_zero h)
  have hf' := isChowFormInt_basis _ b (Pi.basisFun ℚ (Fin 2)) hf
  rw [imageIdeal_std] at hf'
  exact not_isChowFormInt_line_zero hf'

theorem countVol_two_pow {d a : ℕ} (ha : a ≠ 0) :
    countVol 1 d a (fun τ => ((2 ^ (τ ^ 2) : ℕ) : ℕ∞)) = ENNReal.ofReal (Real.log 2) / d := by
  rw [countVol, ← limsup_const (f := (atTop : Filter ℕ)) (ENNReal.ofReal (Real.log 2) / d)]
  refine limsup_congr ((eventually_ne_atTop 0).mono fun k hk => ?_)
  have h0 : ((a * k : ℕ) : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (mul_ne_zero ha hk))
  have h1 : ((a * k : ℕ) : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [logCard_coe, Nat.cast_pow, Real.log_pow, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    Nat.factorial_one, Nat.cast_one, one_mul, Nat.cast_pow, mul_comm _ (ENNReal.ofReal _),
    ENNReal.mul_div_mul_right _ _ h0 h1]
  norm_num

theorem volSlope_zero {δ : ℝ} : volSlope δ (fun _ => 0) = ⊥ := by
  rw [volSlope, EReal.eq_bot_iff_forall_lt]
  intro y
  refine (iInf_le _ (1 - y)).trans_lt ?_
  simp only [ENNReal.zero_div, EReal.coe_ennreal_zero, zero_sub, ← EReal.coe_neg, EReal.coe_lt_coe_iff]
  linarith

theorem dim_count (p q : ℕ) : p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q) * (p + q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  ring

theorem isShortGen_std (N : ℕ) : IsShortGen (stdNorm N) (stdLat N) (Pi.basisFun ℚ (Fin N)) 1 := by
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun i σ => ?_, le_rfl⟩
  · induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective a
      have : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast _ n
      rw [this, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_le_restrictScalars ℤ (𝓞 ℚ) _ hx
  · simp [stdNorm, Pi.single_apply, apply_ite]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exps_stdWt (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0).1 (τ.1, i) = (Dw.p + Dw.q : ℤ) - 1 - i ∧
      (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0).1 (conjEmb τ.1, j) = -(j : ℤ) := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]
  simp only [stdWt]
  omega

theorem exps_hodgeWt (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (hodgeWt Dw) 0).1 (τ.1, i) = 0 ∧ (wtOf Dw (hodgeWt Dw) 0).1 (conjEmb τ.1, j) = 1 := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]
  simp [hodgeWt, barWt, hi]

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem valL_vw_one_nonneg (G : WTZ E) (v : Rul Xo c → EReal) (h1 : depth_vw U G v ≠ ⊤) (h2 : depth_vw U G v ≠ ⊥)
    {w : cuspW Xo c U G} (hw : w ∈ latW U G) : 0 ≤ valL_vw U G 1 v w := by
  rw [valL_vw, Nat.cast_one, one_mul, EReal.sub_nonneg (Or.inr h1) (Or.inr h2)]
  exact iInf₂_le w hw

theorem valL_vw_base (G : WTZ E) (v : Rul Xo c → EReal) (h : depth_vw U G v = ⊤) (τ : ℕ) (t : Rul Xo c) :
    valL_vw U G (τ + 1) v t = ⊥ := by
  rw [valL_vw, h, EReal.mul_top_of_pos (by exact_mod_cast Nat.succ_pos τ), EReal.sub_top]

end GlobalTheory.CompHt.Test
