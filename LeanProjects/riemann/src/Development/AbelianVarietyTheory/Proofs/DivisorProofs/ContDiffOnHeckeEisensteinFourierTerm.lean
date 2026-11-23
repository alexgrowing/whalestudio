import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

def term (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y t : ℝ) : ℂ :=
  ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) * (y : ℂ) ^ m *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem u_ne {y : ℝ} (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hy this

theorem hasDerivAt_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (fun y => term σ ν a b m y t)
      (-(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t) y := by
  have hu := u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (t : ℂ) + (y : ℂ) * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (t : ℂ)
  have h2 : HasDerivAt (fun y : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a)
      ((a : ℂ) * ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ (a - 1) * (-(((t : ℂ) + (y : ℂ) * I) ^ 2)⁻¹ * I)) y :=
    (((hasDerivAt_inv hu).comp y h1).pow a)
  have h3 : HasDerivAt (fun y : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * y : ℝ) : ℂ) y := by
    have : HasDerivAt (fun y : ℝ => t ^ 2 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add (t ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp y h3
  have h5 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ m) ((m : ℂ) * (y : ℂ) ^ (m - 1)) y :=
    (hasDerivAt_pow m (y : ℂ)).comp_ofReal
  have h := ((h2.mul h4).mul h5).mul_const (Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))))
  refine h.congr_deriv ?_
  simp only [term, Function.comp_def, Pi.mul_apply, ← inv_pow]
  generalize ((t : ℂ) + (y : ℂ) * I)⁻¹ = v
  rw [show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  rcases a with _ | a <;> rcases m with _ | m <;>
    simp only [Nat.add_sub_cancel, Nat.zero_sub, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add,
      neg_zero, Complex.ofReal_mul, Complex.ofReal_ofNat] <;> push_cast <;> ring

theorem continuous_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (term σ ν a b m y) := by
  unfold term
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a :=
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).inv₀ (u_ne hy)).pow a
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact ((h1.mul h2).mul continuous_const).mul (by fun_prop)

theorem norm_term_le (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a b m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) : ∃ bd : ℝ → ℝ, MeasureTheory.Integrable bd ∧
      ∀ t, ∀ y ∈ Metric.ball y₀ (|y₀| / 2), ‖term σ ν a b m y t‖ ≤ bd t := by
  have hσ' : -1 / 2 < σ.re := hσ
  set c := |y₀| / 2 with hc
  have hc0 : 0 < c := by positivity
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (c ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine ⟨fun t => (3 * c) ^ m * κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2), ?_, ?_⟩
  · exact (integrable_rpow_neg_one_add_norm_sq (by simp; linarith)).const_mul _
  intro t y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hyl : c ≤ |y| := by
    have := abs_sub_abs_le_abs_sub y₀ y
    rw [abs_sub_comm] at this; rw [hc]; linarith
  have hyu : |y| ≤ 3 * c := by
    have := abs_sub_abs_le_abs_sub y y₀
    rw [hc]; linarith
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hyl; linarith
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  have hnorm : ‖term σ ν a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m := by
    unfold term
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one, he, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
      ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
    congr 2
    simp
    ring
  rw [hnorm]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ c ^ 2 := min_le_right _ _
    have h3 : c ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hyl 2
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  have hB : |y| ^ m ≤ (3 * c) ^ m := pow_le_pow_left₀ (abs_nonneg y) hyu m
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * (3 * c) ^ m :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := by ring

theorem ne_zero_of_mem_ball {y₀ y : ℝ} (hy₀ : y₀ ≠ 0) (hy : y ∈ Metric.ball y₀ (|y₀| / 2)) : y ≠ 0 := by
  rintro rfl
  rw [Metric.mem_ball, Real.dist_eq, zero_sub, abs_neg] at hy
  have : 0 < |y₀| := abs_pos.2 hy₀
  linarith

theorem integrable_term (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) : MeasureTheory.Integrable (term σ ν a b m y) := by
  obtain ⟨bd, hbd, h⟩ := norm_term_le σ hσ ν a b m hab hy
  exact hbd.mono' (continuous_term σ ν a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => h t y (Metric.mem_ball_self (by positivity)))

def intT (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y : ℝ) : ℂ := ∫ t : ℝ, term σ ν a b m y t

theorem hasDerivAt_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) :
    HasDerivAt (intT σ ν a b m)
      (-(a : ℂ) * I * intT σ ν (a + 1) b m y₀ + 2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀
        + (m : ℂ) * intT σ ν a b (m - 1) y₀) y₀ := by
  obtain ⟨b1, hb1, h1⟩ := norm_term_le σ hσ ν (a + 1) b m (by omega) hy₀
  obtain ⟨b2, hb2, h2⟩ := norm_term_le σ hσ ν a (b + 1) (m + 1) (by omega) hy₀
  obtain ⟨b3, hb3, h3⟩ := norm_term_le σ hσ ν a b (m - 1) hab hy₀
  have i1 := integrable_term σ hσ ν m (a := a + 1) (b := b) (by omega) hy₀
  have i2 := integrable_term σ hσ ν (m + 1) (a := a) (b := b + 1) (by omega) hy₀
  have i3 := integrable_term σ hσ ν (m - 1) (a := a) (b := b) hab hy₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun y t => term σ ν a b m y t)
    (F' := fun y t => -(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t)
    (bound := fun t => ‖-(a : ℂ) * I‖ * b1 t + ‖2 * (-σ - (b : ℂ))‖ * b2 t + ‖(m : ℂ)‖ * b3 t)
    (Metric.ball_mem_nhds y₀ (by positivity))
    (Filter.eventually_of_mem (isOpen_ne.mem_nhds hy₀) fun y hy => (continuous_term σ ν a b m hy).aestronglyMeasurable)
    (integrable_term σ hσ ν m hab hy₀)
    ((((continuous_term σ ν _ _ _ hy₀).const_mul _).add ((continuous_term σ ν _ _ _ hy₀).const_mul _)).add
      ((continuous_term σ ν _ _ _ hy₀).const_mul _)).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t y hy => by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
        rw [norm_mul] <;> gcongr
      · exact h1 t y hy
      · exact h2 t y hy
      · exact h3 t y hy)
    (((hb1.const_mul _).add (hb2.const_mul _)).add (hb3.const_mul _))
    (MeasureTheory.ae_of_all _ fun t y hy => hasDerivAt_term σ ν a b m (ne_zero_of_mem_ball hy₀ hy) t)
  have k2 := key.2
  have hI : (∫ t, (-(a : ℂ) * I * term σ ν (a + 1) b m y₀ t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y₀ t
        + (m : ℂ) * term σ ν a b (m - 1) y₀ t)) = -(a : ℂ) * I * intT σ ν (a + 1) b m y₀ +
        2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀ + (m : ℂ) * intT σ ν a b (m - 1) y₀ := by
    unfold intT
    rw [MeasureTheory.integral_add _ (i3.const_mul _), MeasureTheory.integral_add (i1.const_mul _) (i2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact (i1.const_mul _).add (i2.const_mul _)
  rw [hI] at k2
  exact k2

theorem contDiffOn_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ∀ n : ℕ, ∀ a b m : ℕ, 2 ≤ a + 2 * b → ContDiffOn ℝ n (intT σ ν a b m) {y | y ≠ 0} := by
  intro n
  induction n with
  | zero =>
    intro a b m hab
    exact contDiffOn_zero.2 fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro a b m hab
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne]
    refine ⟨fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have c1 := (contDiffOn_const (c := -(a : ℂ) * I)).mul (ih (a + 1) b m (by omega))
    have c2 := (contDiffOn_const (c := 2 * (-σ - (b : ℂ)))).mul (ih a (b + 1) (m + 1) (by omega))
    have c3 := (contDiffOn_const (c := (m : ℂ))).mul (ih a b (m - 1) hab)
    refine ((c1.add c2).add c3).congr fun y hy => ?_
    exact (hasDerivAt_intT σ hσ ν m hab hy).deriv

theorem hTrans_eq (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : hTrans σ ν y = intT σ ν 2 0 0 y := by
  unfold hTrans intT
  congr 1
  funext t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold term phi
  rw [hnu]
  simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
  congr 2
  have hs : 0 < Real.sqrt (t ^ 2 + y ^ 2) := Real.sqrt_pos.2 hQ
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast hQ.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log hQ.le, Real.log_sqrt hQ.le]
  congr 1
  push_cast
  ring

theorem contDiffOn_hTrans (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ContDiffOn ℝ ∞ (hTrans σ ν) {y | y ≠ 0} := by
  refine (contDiffOn_infty.2 fun n => contDiffOn_intT σ hσ ν n 2 0 0 (by norm_num)).congr fun y hy => ?_
  exact hTrans_eq σ ν hy

end GlobalTheory.HeckeTwo.TermSmooth

namespace GlobalTheory.HeckeTwo

theorem fTerm_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ σ ∈ halfPlane,
    ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => fTerm σ z b ν) (upperHalf F) := by
  intro F _ _ b ν hb σ hσ
  unfold fTerm
  refine contDiffOn_prod fun τ _ => ?_
  have he : ContDiff ℝ ∞ (fun z : Emb F → ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ τ))))).cexp
  have hg : ContDiff ℝ ∞ (fun z : Emb F → ℂ => τ b * (z τ).im) :=
    contDiff_const.mul (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ τ))
  have hh : ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => hTrans σ (τ ν) (τ b * (z τ).im)) (upperHalf F) :=
    (TermSmooth.contDiffOn_hTrans σ hσ (τ ν)).comp hg.contDiffOn
      fun z hz => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact he.contDiffOn.mul hh

end GlobalTheory.HeckeTwo
