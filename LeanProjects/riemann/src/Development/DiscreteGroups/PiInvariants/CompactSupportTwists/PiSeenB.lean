import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_sum_mul {ι : Type*} (s : Finset ι) (c f : ι → ℂ) (U V : ℂ) :
    starRingEnd ℂ ((∑ a ∈ s, c a * f a) * U) * V = ∑ a ∈ s, starRingEnd ℂ (c a) * (starRingEnd ℂ (f a * U) * V) := by
  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul]
  ring

theorem conj_self (w : ℂ) : starRingEnd ℂ w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']
  push_cast
  ring

theorem integrable_sq (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {φ : Sm E n} (hφ : φ ∈ π.V)
    (G : ℝ → ℂ) (hG : Continuous G) (R : ℝ) (hGs : ∀ s, R < |s| → G s = 0) :
    Integrable (fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * G (ldet x)) D.ν := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := bdd_of_mem hθ hφ R
  obtain ⟨KG, hKG⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hG.continuousOn
  have hc : Continuous fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * G (ldet x) :=
    (Complex.continuous_ofReal.comp ((((continuous_of_mem π hφ).comp
      (continuous_fst (X := GA E n) (Y := GA E 0))).norm).pow 2)).mul (hG.comp (continuous_ldet (E := E) (n := n)))
  refine integrable_of_ldet hn D _ hc R (Cφ ^ 2 * KG) (fun x hx => by simp [hGs _ hx]) fun x hx => ?_
  have hI : ldet x ∈ Icc (-R) R := abs_le.1 hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hCφ x hx) 2) (hKG _ hI) (norm_nonneg _) (by positivity)

theorem chi_zero_of {N : ℕ} {s : ℝ} (h : (N : ℝ) + 1 < |s|) : chi N s = 0 := chi_eq_zero h.le

theorem poly_vanish (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {φ : Sm E n} (hφ : φ ∈ π.V)
    (z : ℂ) (N : ℕ)
    (h : ∀ k : ℕ, ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν = 0)
    (q : Polynomial ℝ) :
    ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν = 0 := by
  have e : ∀ x : H E n 0, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) =
      ∑ k ∈ Finset.range (q.natDegree + 1), (q.coeff k : ℂ) *
        (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) * Complex.exp (z * ldet x)) := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, h k, mul_zero]
  · intro k _
    refine Integrable.const_mul ?_ _
    have hi := integrable_sq hn D hθ hφ (fun s => ((chi N s * s ^ k : ℝ) : ℂ) * Complex.exp (z * s))
      ((Complex.continuous_ofReal.comp ((continuous_chi N).mul (continuous_pow k))).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) ((N : ℝ) + 1)
      (fun s hs => by simp [chi_zero_of hs])
    refine hi.congr (Eventually.of_forall fun x => ?_)
    simp only
    ring

theorem sq_zero (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {φ : Sm E n} (hφ : φ ∈ π.V)
    (z : ℂ) (N : ℕ)
    (hpoly : ∀ q : Polynomial ℝ,
      ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν = 0) :
    ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν = 0 := by
  set a : ℝ := (N : ℝ) + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  set B : ℝ := Real.exp (‖z‖ * a) with hB
  have hB0 : 0 < B := Real.exp_pos _
  set ε : ℝ := 1 / (4 * B) with hε
  have hε0 : 0 < ε := by positivity
  have hre : Continuous fun s : ℝ => (Complex.exp (-(z * s))).re :=
    Complex.continuous_re.comp (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
  have him : Continuous fun s : ℝ => (Complex.exp (-(z * s))).im :=
    Complex.continuous_im.comp (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
  obtain ⟨p1, hp1⟩ := exists_polynomial_near_of_continuousOn (-a) a _ hre.continuousOn ε hε0
  obtain ⟨p2, hp2⟩ := exists_polynomial_near_of_continuousOn (-a) a _ him.continuousOn ε hε0

  have hpt : ∀ s : ℝ, |s| ≤ a →
      ‖1 - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ)) * Complex.exp (z * s)‖ ≤ 1 / 2 := by
    intro s hs
    have hsI : s ∈ Icc (-a) a := abs_le.1 hs
    have h1 : ‖Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))‖ ≤ 2 * ε := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e1 : (Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))).re =
          (Complex.exp (-(z * s))).re - p1.eval s := by simp
      have e2 : (Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))).im =
          (Complex.exp (-(z * s))).im - p2.eval s := by simp
      rw [e1, e2, abs_sub_comm _ (p1.eval s), abs_sub_comm _ (p2.eval s)]
      linarith [hp1 s hsI, hp2 s hsI]
    have h2 : ‖Complex.exp (z * s)‖ ≤ B := by
      rw [Complex.norm_exp, hB]
      refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    have e3 : 1 - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ)) * Complex.exp (z * s) =
        Complex.exp (z * s) * (Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))) := by
      rw [mul_sub, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      ring
    rw [e3, norm_mul]
    calc ‖Complex.exp (z * s)‖ * ‖Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))‖
        ≤ B * (2 * ε) := mul_le_mul h2 h1 (norm_nonneg _) hB0.le
      _ = 1 / 2 := by rw [hε]; field_simp; ring

  have hΦ := integrable_sq hn D hθ hφ (fun s => ((chi N s : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_chi N)) a (fun s hs => by simp [chi_zero_of hs])
  have hr : Integrable (fun x : H E n 0 => ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) D.ν := by
    refine hΦ.norm.congr (Eventually.of_forall fun x => ?_)
    show ‖((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ)‖ = ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (chi_nonneg _ _)]
  have hT0 : 0 ≤ ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν :=
    integral_nonneg fun x => mul_nonneg (by positivity) (chi_nonneg _ _)
  set T := ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν with hT
  have hP1 := hpoly p1
  have hP2 := hpoly p2
  have hint : ∀ q : Polynomial ℝ, Integrable (fun x : H E n 0 =>
      ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x)) D.ν := fun q => by
    have hi := integrable_sq hn D hθ hφ (fun s => ((chi N s * q.eval s : ℝ) : ℂ) * Complex.exp (z * s))
      ((Complex.continuous_ofReal.comp ((continuous_chi N).mul (Polynomial.continuous q))).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) a
      (fun s hs => by simp [chi_zero_of hs])
    refine hi.congr (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hcomb : (T : ℂ) = ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) *
      (1 - (((p1.eval (ldet x) : ℝ) : ℂ) + Complex.I * ((p2.eval (ldet x) : ℝ) : ℂ)) * Complex.exp (z * ldet x)) ∂D.ν := by
    have e0 : (T : ℂ) = ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) ∂D.ν := by
      rw [hT, ← integral_complex_ofReal]
      simp only [Complex.ofReal_mul]
    rw [e0]
    have e1 : (∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) *
        (1 - (((p1.eval (ldet x) : ℝ) : ℂ) + Complex.I * ((p2.eval (ldet x) : ℝ) : ℂ)) * Complex.exp (z * ldet x)) ∂D.ν) =
        (∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) ∂D.ν) -
          ((∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p1.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν) +
            Complex.I * ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) *
              Complex.exp (z * ldet x) ∂D.ν) := by
      have hΦ' : Integrable (fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ)) D.ν := hΦ
      have hpt2 : (fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) *
          (1 - (((p1.eval (ldet x) : ℝ) : ℂ) + Complex.I * ((p2.eval (ldet x) : ℝ) : ℂ)) * Complex.exp (z * ldet x))) =
          fun x => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) -
            (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p1.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) +
              Complex.I * (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) *
                Complex.exp (z * ldet x))) := by
        funext x
        push_cast
        ring
      have hsum : Integrable (fun x : H E n 0 =>
          ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p1.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) +
            Complex.I * (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) *
              Complex.exp (z * ldet x))) D.ν := (hint p1).add ((hint p2).const_mul Complex.I)
      have hI2 : Integrable (fun x : H E n 0 => Complex.I * (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) *
          ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x))) D.ν := (hint p2).const_mul Complex.I
      rw [hpt2, integral_sub hΦ' hsum,
        integral_add (hint p1) hI2, integral_const_mul]
    rw [e1, hP1, hP2]
    ring
  have hle : ‖(T : ℂ)‖ ≤ ∫ x, (1 / 2 : ℝ) * (‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) ∂D.ν := by
    rw [hcomb]
    refine norm_integral_le_of_norm_le (hr.const_mul _) (Eventually.of_forall fun x => ?_)
    by_cases hx : |ldet x| ≤ a
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_nonneg (chi_nonneg _ _)]
      have := hpt _ hx
      have h0 : 0 ≤ ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) := mul_nonneg (by positivity) (chi_nonneg _ _)
      nlinarith
    · rw [chi_zero_of (lt_of_not_ge hx)]
      simp
  rw [integral_const_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0] at hle
  linarith

end DiscreteGroups.T1.G.Dcy

end
