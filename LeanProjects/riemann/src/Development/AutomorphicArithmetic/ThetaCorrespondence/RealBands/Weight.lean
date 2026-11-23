import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsCompactBall
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private lemma wt_le {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (x : MatrixCoordinates n)
    (h : hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4) :
    (wt g)⁻¹ ≤ (Real.sqrt n + 1) ^ (2 * n ^ 2 + 1) * (1 + ‖x‖) ^ (-((2 * n ^ 2 + 1 : ℕ) : ℝ)) := by
  set R : ℝ := Real.sqrt (hs (umat g)) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hs0 : 0 ≤ hs (umat g) := by unfold hs; positivity
  have hg : hs (coeMatrixAlt ε g) ≤ R ^ 2 := by rw [hR, Real.sq_sqrt hs0]; exact le_rfl
  have hn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ R * (Real.sqrt n + 1) := by positivity
  have hx : ‖x‖ ≤ R * (Real.sqrt n + 1) := by
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro j
    have := norm_entry_mul_near_one_le (g := coeMatrixAlt ε g) hR0 hg h i j
    rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
    exact this
  have h1 : 1 + ‖x‖ ≤ (Real.sqrt n + 1) * (1 + R) := by nlinarith
  have h2 : (1 + ‖x‖) ^ (2 * n ^ 2 + 1) ≤ (Real.sqrt n + 1) ^ (2 * n ^ 2 + 1) * wt g := by
    unfold wt
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  have hw : 0 < wt g := by unfold wt; positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hw (by positivity), one_mul]
  exact h2

private lemma slice_le {n : ℕ} {ε : Fin n → Bool} (S : Subgroup (UJ ε)) (ν : Measure (UJ ε))
    (hν : IsHaarSub (S : Set (UJ ε)) ν) (x : MatrixCoordinates n) :
    ν {g | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} ≤
      ν {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2} := by
  obtain ⟨-, -, h0, hinv⟩ := hν
  set A : Set (UJ ε) := {g | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} with hA
  set W : Set (UJ ε) := {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2} with hW
  have hWm : MeasurableSet W :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  by_cases hne : (A ∩ (S : Set (UJ ε))).Nonempty
  · obtain ⟨h, hh, hS⟩ := hne
    calc ν A ≤ ν ((fun g => h⁻¹ * g) ⁻¹' W) := by
          refine measure_mono fun g hg => ?_
          show hs (coeMatrixAlt ε (h⁻¹ * g)) ≤ _
          refine frobenius_bound_of_mul_near_one hg hh ?_
          rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
            determinant_character_mul_inv, Matrix.mul_one]
      _ = ν.map (fun g => h⁻¹ * g) W := (Measure.map_apply (measurable_const_mul _) hWm).symm
      _ = ν W := by rw [hinv h⁻¹ (S.inv_mem hS)]
  · have : ν A = 0 := measure_mono_null (fun g hg hS => hne ⟨g, hg, hS⟩) h0
    rw [this]
    exact bot_le

theorem UpperTheory.Lit.Cusp.integrable_wt :
    ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (ν : Measure (UJ ε)), IsHaarSub (S : Set (UJ ε)) ν →
      Integrable (fun g : UJ ε => (wt g)⁻¹) ν := by
  intro n ε S ν hν
  classical
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  let lam : Measure (MatrixCoordinates n) := Measure.addHaar
  let O : Set (MatrixCoordinates n) := {x | hs (Matrix.of x - 1) < 1 / 4}
  let W : Set (UJ ε) := {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2}
  have hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x) := continuous_id
  have hO_open : IsOpen O :=
    isOpen_lt (continuous_hs_real_place_taylor.comp (hof.sub continuous_const)) continuous_const
  have hO_pos : 0 < lam O := hO_open.measure_pos lam ⟨Matrix.of.symm 1, by simp [O, hs]⟩
  have hW_fin : ν W < ⊤ := by
    have hc : IsCompact W := by
      have := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage
        ((hermitian_small_ball n ε).1 ((2 * Real.sqrt n + 1) ^ 2))
      convert this using 1
      ext g
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    exact hc.measure_lt_top
  have hwpos : ∀ g : UJ ε, 0 < wt g := fun g => by unfold wt; positivity
  have hwc : Continuous fun g : UJ ε => (wt g)⁻¹ := by
    refine Continuous.inv₀ ?_ fun g => (hwpos g).ne'
    exact (continuous_const.add (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).sqrt).pow _
  let w : UJ ε → ENNReal := fun g => ENNReal.ofReal (wt g)⁻¹
  have hwm : Measurable w := hwc.measurable.ennreal_ofReal
  let U : Set (UJ ε × MatrixCoordinates n) := {p | hs (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2 - 1) < 1 / 4}
  have hU : MeasurableSet U :=
    (isOpen_lt (continuous_hs_real_place_taylor.comp ((((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd)).sub continuous_const)) continuous_const).measurableSet
  let f : UJ ε → MatrixCoordinates n → ENNReal := fun g x => U.indicator (fun p => w p.1) (g, x)
  have hf : Measurable (Function.uncurry f) := (hwm.comp measurable_fst).indicator hU
  have h1 : ∫⁻ g, ∫⁻ x, f g x ∂lam ∂ν = (∫⁻ g, w g ∂ν) * lam O := by
    rw [← lintegral_mul_const _ hwm]
    refine lintegral_congr fun g => ?_
    have hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1 := det_leftMulReal_eq_one (g⁻¹).2
    have e : f g = (leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O).indicator fun _ => w g := by
      funext x
      rfl
    have hm : MeasurableSet (leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O) :=
      (hO_open.preimage (LinearMap.continuous_of_finiteDimensional _)).measurableSet
    rw [e, lintegral_indicator_const hm,
      Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let c : ENNReal := ENNReal.ofReal ((Real.sqrt n + 1) ^ (2 * n ^ 2 + 1))
  let b : MatrixCoordinates n → ENNReal := fun x => ENNReal.ofReal ((1 + ‖x‖) ^ (-((2 * n ^ 2 + 1 : ℕ) : ℝ)))
  have hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2 := by
    simp [MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hb : ∫⁻ x, b x ∂lam < ⊤ :=
    finite_integral_one_add_norm (by rw [hfr]; exact_mod_cast Nat.lt_succ_self _)
  have h2 : ∀ x, ∫⁻ g, f g x ∂ν ≤ (c * ν W) * b x := by
    intro x
    have hm : MeasurableSet {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} :=
      measurable_prodMk_right hU
    calc ∫⁻ g, f g x ∂ν
        ≤ ∫⁻ g, {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4}.indicator
            (fun _ => c * b x) g ∂ν := by
          refine lintegral_mono fun g => ?_
          by_cases hg : hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4
          · have hgU : (g, x) ∈ U := hg
            simp only [f]
            rw [Set.indicator_of_mem hgU, Set.indicator_of_mem (by exact hg)]
            simp only [w, c, b]
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (wt_le g x hg)
          · have hgU : (g, x) ∉ U := hg
            simp only [f]
            rw [Set.indicator_of_notMem hgU]
            exact bot_le
      _ = c * b x * ν {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} :=
          lintegral_indicator_const hm _
      _ ≤ c * b x * ν W := mul_le_mul' le_rfl (slice_le S ν hν x)
      _ = (c * ν W) * b x := by ring
  have hcW : c * ν W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_fin.ne
  have h3 : (∫⁻ g, w g ∂ν) * lam O < ⊤ := by
    rw [← h1, lintegral_lintegral_swap hf.aemeasurable]
    refine (lintegral_mono h2).trans_lt ?_
    rw [lintegral_const_mul' _ _ hcW]
    exact ENNReal.mul_lt_top hcW.lt_top hb
  have h4 : ∫⁻ g, w g ∂ν < ⊤ := ENNReal.lt_top_of_mul_ne_top_left h3.ne hO_pos.ne'
  refine ⟨hwc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => inv_nonneg.2 (hwpos g).le)]
  exact h4
