import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol

def I0 : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹)

theorem I0_lt_top : I0 < ⊤ := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun z => ?_
  congr 1
  rw [Real.rpow_neg (by positivity), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]

def wt (l : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹ * ((1 + |l| * ‖z‖) ^ 3)⁻¹)

theorem measurable_wt (l : ℝ) : Measurable (wt l) := by
  unfold wt
  fun_prop

theorem lint_scale {l : ℝ} (hl : l ≠ 0) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) = ENNReal.ofReal ((l ^ 2)⁻¹) * I0 := by
  have hr : |l| ≠ 0 := abs_ne_zero.mpr hl
  have hm := Measure.map_addHaar_smul (volume : Measure ℂ) hr
  have hF : Measurable fun w : ℂ => ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) := by fun_prop
  have h1 : ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹)
      = ∫⁻ w : ℂ, ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) ∂(Measure.map (fun x : ℂ => |l| • x) volume) := by
    rw [lintegral_map hF (measurable_const_smul _)]
    refine lintegral_congr fun z => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_abs]
  rw [h1, hm, lintegral_smul_measure, Complex.finrank_real_complex]
  simp only [smul_eq_mul, I0]
  congr 2
  rw [abs_of_nonneg (by positivity), sq_abs]

theorem one_var (l : ℝ) :
    ∫⁻ z : ℂ, wt l z ≤ ENNReal.ofReal (2 * I0.toReal * (1 + l ^ 2)⁻¹) := by
  have hI : ENNReal.ofReal I0.toReal = I0 := ENNReal.ofReal_toReal I0_lt_top.ne
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rcases le_or_gt |l| 1 with h | h
  · have h1 : ∫⁻ z : ℂ, wt l z ≤ I0 := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + |l| * ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by nlinarith [norm_nonneg z, abs_nonneg l]))
      nlinarith
    refine h1.trans ?_
    conv_lhs => rw [← hI]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : l ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg l]
    have h3 : (1 : ℝ) ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · have hl : l ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    have h1 : ∫⁻ z : ℂ, wt l z ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + |l| * ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by linarith [norm_nonneg z]))
      nlinarith
    refine h1.trans ?_
    rw [lint_scale hl]
    conv_lhs => rw [← hI]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 1 ≤ l ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h3 : (l ^ 2)⁻¹ ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    nlinarith

theorem pi_bound {n : ℕ} (l : Fin n → ℝ) :
    ∫⁻ z : Fin n → ℂ, ∏ i, wt (l i) (z i) ≤
      ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod
    (f := fun i => wt (l i)) fun i => (measurable_wt (l i)).aemeasurable]
  refine (Finset.prod_le_prod' fun i _ => one_var (l i)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib]

theorem prod_le_pow {n K : ℕ} (hK : 3 * n ≤ K) {x : Fin n → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ a) (ha : 0 ≤ a) :
    ((1 + a) ^ K)⁻¹ ≤ ∏ i, ((1 + x i) ^ 3)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by have := h0 i; positivity) ?_
  calc ∏ i, (1 + x i) ^ 3 ≤ ∏ _i : Fin n, (1 + a) ^ 3 :=
        Finset.prod_le_prod (fun i _ => by have := h0 i; positivity)
          fun i _ => pow_le_pow_left₀ (by have := h0 i; positivity) (by linarith [hx i]) 3
    _ = (1 + a) ^ (3 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ (1 + a) ^ K := pow_le_pow_right₀ (by linarith) hK

theorem weight_le {n K : ℕ} (hK : 3 * n ≤ K) (l : Fin n → ℝ) {a d : ℝ} (z : Fin n → ℂ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (h1 : ∀ i, ‖z i‖ ≤ a) (h2 : ∀ i, |l i| * ‖z i‖ ≤ d) :
    ENNReal.ofReal (((1 + a) ^ K)⁻¹ * ((1 + d) ^ K)⁻¹) ≤ ∏ i, wt (l i) (z i) := by
  unfold wt
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul (prod_le_pow hK (fun i => norm_nonneg _) h1 ha)
    (prod_le_pow hK (fun i => by positivity) h2 hd) (by positivity)
    (Finset.prod_nonneg fun i _ => by positivity)

theorem det_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    det ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) = det X := by
  rw [det_mul, det_mul, mul_comm (det (U : Matrix (Fin n) (Fin n) ℂ)), mul_assoc, ← det_mul,
    mem_unitaryGroup_iff.mp U.2, det_one, mul_one]

theorem detW_eq {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    detW b = ∏ i, (1 + hb.eigenvalues i ^ 2) := by
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hb.eigenvalues) with hD
  have hs := hb.spectral_theorem
  have h1 : 1 + b * b = Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary (1 + D * D) := by
    rw [map_add, map_one, map_mul, ← hs]
  have h2 : 1 + D * D = diagonal fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    ext i
    simp [sq]
  rw [detW, h1, Unitary.conjStarAlgAut_apply, det_conj_unitary, h2, det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem repr_apply_lin {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hb.eigenvectorBasis.repr (Matrix.toEuclideanLin b y) i =
      (hb.eigenvalues i : ℂ) * hb.eigenvectorBasis.repr y i := by
  have hs : (Matrix.toEuclideanLin b).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hb
  have he : Matrix.toEuclideanLin b (hb.eigenvectorBasis i) =
      (hb.eigenvalues i : ℂ) • hb.eigenvectorBasis i := by
    have := hb.mulVec_eigenvectorBasis i
    apply PiLp.ext
    intro j
    have h2 := congrFun this j
    simpa [toLpLin_apply] using h2
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hs, he, inner_smul_left]
  simp

theorem map_isometry {n : ℕ} (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure]
    (R : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving R m m := by
  have hp := LinearIsometryEquiv.measurePreserving
    (⟨R.toLinearEquiv.restrictScalars ℝ, R.norm_map⟩ :
      EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
  have hc := Measure.isAddLeftInvariant_eq_smul m (volume : Measure (EuclideanSpace ℂ (Fin n)))
  refine ⟨R.continuous.measurable, ?_⟩
  have hm : Measure.map R (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := hp.map_eq
  conv_lhs => rw [hc]
  rw [Measure.map_smul, hm, ← hc]

theorem exists_scale (n : ℕ) (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure] :
    ∃ c : NNReal, ∀ P : (Fin n → ℂ) → ℝ≥0∞, Measurable P →
      ∫⁻ y, P (WithLp.ofLp y) ∂m = c * ∫⁻ x, P x := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  haveI : (Measure.map e m).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e m = c • (volume : Measure (Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun P hP => ?_⟩
  have h1 : ∫⁻ y, P (WithLp.ofLp y) ∂m = ∫⁻ x, P x ∂(Measure.map e m) := by
    rw [lintegral_map hP e.continuous.measurable]
    rfl
  rw [h1, hc, lintegral_smul_measure]
  rfl

theorem volume_bound : ∀ (n K : ℕ), 3 * n ≤ K → ∀ m : Measure (EuclideanSpace ℂ (Fin n)), m.IsAddHaarMeasure →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ∂m ≤
      ENNReal.ofReal (C * (detW b)⁻¹) := by
  intro n K hK m hm
  obtain ⟨c, hc⟩ := exists_scale n m
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  refine ⟨c * (2 * I0.toReal) ^ n, by positivity, fun b hb => ?_⟩
  set l := hb.eigenvalues with hl
  set R := hb.eigenvectorBasis.repr with hR
  let P : (Fin n → ℂ) → ℝ≥0∞ := fun x => ∏ i, wt (l i) (x i)
  have hP : Measurable P :=
    Finset.measurable_prod _ fun i _ => (measurable_wt (l i)).comp (measurable_pi_apply i)
  have hG : Measurable fun y : EuclideanSpace ℂ (Fin n) => P (WithLp.ofLp y) :=
    hP.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable
  have h1 : ∀ y : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ≤
        P (WithLp.ofLp (R y)) := by
    intro y
    refine weight_le hK l _ (norm_nonneg _) (norm_nonneg _) (fun i => ?_) (fun i => ?_)
    · rw [← R.norm_map y]
      exact PiLp.norm_apply_le (R y) i
    · rw [← R.norm_map (Matrix.toEuclideanLin b y)]
      refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le (R (Matrix.toEuclideanLin b y)) i)
      rw [hR, repr_apply_lin hb, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ∫⁻ y, P (WithLp.ofLp (R y)) ∂m := lintegral_mono h1
    _ = ∫⁻ y, P (WithLp.ofLp y) ∂m := (map_isometry m R).lintegral_comp hG
    _ = c * ∫⁻ x, P x := hc P hP
    _ ≤ c * ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
        gcongr
        exact pi_bound l
    _ = ENNReal.ofReal (c * (2 * I0.toReal) ^ n * (detW b)⁻¹) := by
        rw [detW_eq hb, mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ)) (by positivity),
          ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol
