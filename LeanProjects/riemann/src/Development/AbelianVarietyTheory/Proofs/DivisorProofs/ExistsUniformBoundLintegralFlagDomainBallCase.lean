import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLastStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOneSubOffDiagonalBlockGramLeOneBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankFourLtTopStatement

namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
  GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped ENNReal Matrix

theorem prod_inv_sq_mul_rpow_le {q : ℕ} {t s : ℝ} (d g : Fin q → ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hs : 2 * (q : ℝ) ≤ s) (hg : ∀ k, 0 < g k) (hdg : ∀ k, t * g k ≤ d k) :
    (∏ k, (d k ^ 2)⁻¹) * t ^ s ≤ ∏ k, g k ^ (-2 : ℤ) := by
  have h1 : ∏ k, (d k ^ 2)⁻¹ ≤ ∏ k, (t ^ 2)⁻¹ * (g k ^ 2)⁻¹ := by
    refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by have := hg k; positivity) (pow_le_pow_left₀ (by have := hg k; positivity) (hdg k) 2)
  have h2 : t ^ s ≤ t ^ (2 * (q : ℝ)) := Real.rpow_le_rpow_of_exponent_ge ht ht1 hs
  have h3 : t ^ (2 * (q : ℝ)) = (t ^ 2) ^ q := by
    rw [Real.rpow_mul ht.le, Real.rpow_two, Real.rpow_natCast]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  calc (∏ k, (d k ^ 2)⁻¹) * t ^ s ≤ ((t ^ 2)⁻¹ ^ q * ∏ k, (g k ^ 2)⁻¹) * (t ^ 2) ^ q := by
        refine mul_le_mul h1 (h2.trans h3.le) (by positivity) (by positivity)
    _ = ∏ k, g k ^ (-2 : ℤ) := by
        rw [mul_comm, ← mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), one_mul]
        exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_ofNat]

theorem prod_fin_split {r : ℕ} (hr : 1 ≤ r) (f : Fin r → ℝ) :
    ∏ i, f i = f ⟨0, by omega⟩ * ∏ k : Fin (r - 1), f ⟨k + 1, by omega⟩ := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  rw [Fin.prod_univ_succ]
  rfl

theorem colGram_zero {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) : colGram M 0 = 1 := by
  simp [colGram, lminor, Matrix.det_isEmpty]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_dmin_zero (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (h : 0 < r + 1) :
    ‖dmin X.Gm x τ ⟨0, h⟩‖ = 1 := by
  simp [dmin, lminor, Matrix.det_isEmpty]

theorem ball_cases {X : Data E r} (h1 : 0 < X.p0) (h2 : X.p0 < r) (h3 : X.p0 * (r - X.p0) ≤ 3) :
    X.p0 = 1 ∨ X.p0 + 1 = r := by
  by_contra hc
  push_neg at hc
  have ha : 2 ≤ X.p0 := by omega
  have hb : 2 ≤ r - X.p0 := by omega
  have := Nat.mul_le_mul ha hb
  omega

theorem exp_neg_rho {X : Data E r} {z : V (nd X)} (hz : z ∈ Om X) (s : ℝ) :
    Real.exp (-(s * rho X z)) = ∏ τ, zDet X z τ ^ s := by
  have e : -(s * rho X z) = ∑ τ, Real.log (zDet X z τ) * s := by
    simp only [rho, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e, Real.exp_sum]
  exact Finset.prod_congr rfl fun τ _ => (Real.rpow_def_of_pos (zDet_pos X hz τ) s).symm

theorem density_mul_exp_le (X : Data E r) (h1 : 0 < X.p0) (h2 : X.p0 < r) (h3 : X.p0 * (r - X.p0) ≤ 3)
    (x0 : Base X) {z : V (nd X)} (hz : z ∈ Om X) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    density X x0 z * Real.exp (-(s * rho X z)) ≤ bnd X z := by
  have hcase := ball_cases h1 h2 h3
  have hq : 2 * ((r - 1 : ℕ) : ℝ) ≤ s := by
    rw [Nat.cast_sub (by omega)]
    simpa using hs
  have hle : ∀ τ, zDet X z τ ≤ 1 := GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball E r X hcase z hz
  unfold density bnd
  rw [exp_neg_rho hz, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun τ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Real.rpow_nonneg (zDet_pos X hz τ).le s)) fun τ _ => ?_
  rw [prod_fin_split (by omega)]
  simp only [Fin.castSucc_mk]
  rw [show (‖dmin X.Gm (point X x0 z) τ ⟨0, by omega⟩‖ ^ 2)⁻¹ = 1 by
    rw [norm_dmin_zero]; norm_num, one_mul]
  rcases hcase with hp | hp
  · exact prod_inv_sq_mul_rpow_le (fun k : Fin (r - 1) => ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖)
      (fun k => colGram (blkW X.p0 (zOf X z τ)) k.castSucc) (zDet_pos X hz τ) (hle τ) hq
      (fun k => GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos r X.p0 _ _) (fun k => GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_first E r X hp x0 z hz τ k)
  · have := prod_inv_sq_mul_rpow_le (fun k : Fin (r - 1) => ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖)
      (fun k => colGram (blkW X.p0 (zOf X z τ)) k.succ) (zDet_pos X hz τ) (hle τ) hq
      (fun k => GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos r X.p0 _ _) (fun k => GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last E r X hp x0 z hz τ k)
    refine this.trans_eq ?_
    have e1 := Fin.prod_univ_succ fun j : Fin (r - 1 + 1) => colGram (blkW X.p0 (zOf X z τ)) j ^ (-2 : ℤ)
    have e2 := Fin.prod_univ_castSucc fun j : Fin (r - 1 + 1) => colGram (blkW X.p0 (zOf X z τ)) j ^ (-2 : ℤ)
    rw [colGram_zero, one_zpow, one_mul] at e1
    rw [GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one r X.p0 (zOf X z τ), one_zpow, mul_one] at e2
    rw [← e1, e2]
    rfl

theorem block_fin {p0 : ℕ} (h1 : 0 < p0) (h2 : p0 < r) (h3 : p0 * (r - p0) ≤ 3) :
    ∫⁻ w : Low r → ℂ, hB p0 w < ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = p0 + k + 1 := ⟨r - p0 - 1, by omega⟩
  have h3' : p0 * (k + 1) ≤ 3 := by simpa [show p0 + k + 1 - p0 = k + 1 by omega] using h3
  have hr : p0 + k ≤ 3 := by nlinarith
  have hp : p0 ≤ 3 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p0 <;> interval_cases k <;> first
    | omega
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top _ (by decide)
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top _ (by decide)

theorem lintegral_lt_top (X : Data E r) (x0 : Base X) (h1 : 0 < X.p0) (h2 : X.p0 < r)
    (h3 : X.p0 * (r - X.p0) ≤ 3) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 < ⊤ := by
  have hm : Measurable fun z : V (nd X) => ∏ τ, hB X.p0 (zOf X z τ) := by
    refine Finset.measurable_prod _ fun τ _ => (GlobalTheory.T.measurable_cutoffGramBoundMixedBlock r X.p0).comp ?_
    exact measurable_pi_lambda _ fun p => (EuclideanSpace.proj (𝕜 := ℂ) _).continuous.measurable
  rw [GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain E r X x0 s]
  calc ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z)))
      ≤ ∫⁻ z in Om X, ∏ τ, hB X.p0 (zOf X z τ) := by
        refine setLIntegral_mono hm fun z hz => ?_
        rw [← ENNReal.ofReal_mul (by unfold density; positivity)]
        exact (ENNReal.ofReal_le_ofReal (density_mul_exp_le X h1 h2 h3 x0 hz hs)).trans
          (GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff E r X z hz)
    _ ≤ ∫⁻ z, ∏ τ, hB X.p0 (zOf X z τ) := setLIntegral_le_lintegral _ _
    _ = ∏ _τ : X.Ψ, ∫⁻ w, hB X.p0 w := GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod E r X _ (GlobalTheory.T.measurable_cutoffGramBoundMixedBlock r X.p0)
    _ < ⊤ := ENNReal.prod_lt_top fun _ _ => block_fin h1 h2 h3

theorem intBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 →
    X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℝ, 2 * ((r : ℝ) - 1) ≤ s → ∃ I : ℝ≥0∞, I < ⊤ ∧
      ∀ x1 : Frame X.Ψ r, IsOrth X x1 →
        ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I := by
  intro E _ _ _ r X h1 h2 h3 s hs
  have h0 : IsOrth X (x0F X) := GlobalTheory.OrthNear.isOrth_x0F X
  refine ⟨_, lintegral_lt_top X ⟨x0F X, h0⟩ h1 h2 h3 hs, fun x1 hx1 => ?_⟩
  rw [GlobalTheory.Up.PoleValue.rhF_eq h0 hx1, GlobalTheory.Up.PoleValue.muF_eq h0 hx1]

end GlobalTheory.IntBall
