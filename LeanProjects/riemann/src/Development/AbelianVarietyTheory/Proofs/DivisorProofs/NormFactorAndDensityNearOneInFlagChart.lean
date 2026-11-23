import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviFinsetSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartNearOne

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_succ_sub_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  linarith

theorem nmat_entry_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖nmat X z τ a b - (if a = b then 1 else 0)‖ ≤ ‖z‖ := by
  unfold nmat
  by_cases h : b < a
  · have hab : a ≠ b := fun e => lt_irrefl b (e ▸ h)
    rw [dif_pos h, if_neg hab, sub_zero]
    exact PiLp.norm_apply_le z _
  · rw [dif_neg h]
    split_ifs <;> simp

theorem det_nmat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [mat, nmat]
  · intro a b hab
    have h1 : ¬ b < a := fun h => lt_asymm h hab
    have h2 : a ≠ b := ne_of_lt hab
    simp [mat, nmat, h1, h2]

theorem norm_dmin_zero (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) : ‖dmin X.Gm y τ 0‖ = 1 := by
  haveI : IsEmpty (Fin ((0 : Fin (r + 1)) : ℕ)) := ⟨fun i => absurd i.2 (by simp)⟩
  rw [dmin, lminor, Matrix.det_isEmpty, norm_one]

theorem norm_dmin_last (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) :
    ‖dmin X.Gm (cpt X x z) τ (Fin.last r)‖ = 1 := by
  rw [PoinPf.dmin_cpt_orth X hx]
  have e : lminor (PoinPf.Gw X z τ) (Fin.last r) = (PoinPf.Gw X z τ).det := rfl
  rw [e, PoinPf.Gw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_nmat,
    show (mat (nmat X z) τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat (nmat X z) τ) from rfl,
    ← RingHom.map_det, det_nmat, PoinPf.Jd, Matrix.det_diagonal]
  simp only [one_mul, map_one, mul_one, norm_prod, Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  simp

theorem abs_sub_mid_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    |(la τ i : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2| ≤ X.spread la τ / 2 := by
  have h1 := le_ciSup (Finite.bddAbove_range fun k => (la τ k : ℝ)) i
  have h2 := ciInf_le (Finite.bddBelow_range fun k => (la τ k : ℝ)) i
  unfold Data.spread
  rw [abs_le]
  constructor <;> linarith

theorem weighted_diff_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (L : Fin (r + 1) → ℝ) {t : ℝ}
    (hL : ∀ i, |L i| ≤ t) (h0 : L 0 = 0) (hr : L (Fin.last r) = 0) :
    ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) ≤ r * t * X.spread la τ := by
  set c := ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2
  have hs : 0 ≤ X.spread la τ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [Data.spread]
    · have := abs_sub_mid_le X la τ ⟨0, hr0⟩
      linarith [abs_nonneg ((la τ ⟨0, hr0⟩ : ℝ) - c)]
  have e : ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) =
      ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc) +
        c * ∑ i : Fin r, (L i.succ - L i.castSucc) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, sum_succ_sub_castSucc, h0, hr, sub_zero, mul_zero, add_zero]
  calc ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc)
      ≤ ∑ i : Fin r, X.spread la τ / 2 * (2 * t) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have h1 := abs_sub (L i.succ) (L i.castSucc)
        have h2 : |L i.succ - L i.castSucc| ≤ 2 * t := by linarith [hL i.succ, hL i.castSucc]
        exact mul_le_mul (abs_sub_mid_le X la τ i) h2 (abs_nonneg _) (by linarith)
    _ = r * t * X.spread la τ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

theorem chart_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w →
    ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧
      Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  intro E _ _ _ r X la w x hr hx hw z hz
  have hf : (1 : ℝ) ≤ fdeg E := one_le_field_half_degree
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsp : ∀ τ, 0 ≤ X.spread la τ := fun τ => by
    have := abs_sub_mid_le X la τ ⟨0, hr⟩
    linarith [abs_nonneg ((la τ ⟨0, hr⟩ : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2)]
  have hw0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => hsp τ) hw
  set δ := chartRad E r w with hδdef
  have hwf : 0 < w + fdeg E := by linarith
  have hδ0 : 0 < δ := by rw [hδdef, chartRad]; positivity
  have key : (r : ℝ) ^ 3 * δ * (w + fdeg E) * 200 = 1 := by
    rw [hδdef, chartRad]
    have : (r : ℝ) ≠ 0 := by positivity
    field_simp
  have hA0 : 0 ≤ (r : ℝ) ^ 3 * δ := by positivity
  have hA : (r : ℝ) ^ 3 * δ ≤ 1 / 200 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ w + fdeg E by linarith) hA0]
  have hr2 : (r : ℝ) ^ 2 * δ ≤ (r : ℝ) ^ 3 * δ := by
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hδ0.le
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) hδ0.le (by linarith)
    (fun τ a b => (nmat_entry_le X z τ a b).trans hz)
  change cpt X x z ∈ X.dom at hdom
  change ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) at hd
  set t := 9 * ((r : ℝ) ^ 2 * δ) with ht
  have ht0 : 0 ≤ t := by positivity
  refine ⟨hdom, ?_, ?_⟩
  ·
    have hne : ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 := fun τ i => (hd τ i).1
    have hN := CurvPf.neg2log_nfac X la (cpt X x z) hne
    have hbound : -2 * Real.log (X.nfac la (cpt X x z)) ≤ r * t * w := by
      rw [hN]
      calc ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Real.log ‖dmin X.Gm (cpt X x z) τ i.succ‖ -
            Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖)
          ≤ ∑ τ, (r : ℝ) * t * X.spread la τ :=
            Finset.sum_le_sum fun τ _ => weighted_diff_le X la τ
              (fun i => Real.log ‖dmin X.Gm (cpt X x z) τ i‖) (fun i => (hd τ i).2)
              (by simp only [norm_dmin_zero, Real.log_one])
              (by simp only [norm_dmin_last X hx, Real.log_one])
        _ = (r : ℝ) * t * ∑ τ, X.spread la τ := (Finset.mul_sum _ _ _).symm
        _ ≤ (r : ℝ) * t * w := mul_le_mul_of_nonneg_left hw (by positivity)
    have hsmall : (r : ℝ) * t * w ≤ 1 / 20 := by
      have e1 : (r : ℝ) * t * w = 9 * ((r : ℝ) ^ 3 * δ * w) := by rw [ht]; ring
      have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * fdeg E := by positivity
      rw [e1]
      nlinarith
    have hpos : 0 < X.nfac la (cpt X x z) := by
      unfold Data.nfac
      exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
        Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hne _ _) (hne _ _))) _
    have e : X.nfac la (cpt X x z) ^ 2 = Real.exp (-(-2 * Real.log (X.nfac la (cpt X x z)))) := by
      rw [show -(-2 * Real.log (X.nfac la (cpt X x z))) =
        Real.log (X.nfac la (cpt X x z)) + Real.log (X.nfac la (cpt X x z)) by ring,
        Real.exp_add, Real.exp_log hpos, sq]
    rw [e]
    exact Real.exp_le_exp.2 (by linarith)
  ·
    have hfac : ∀ τ (i : Fin r), Real.exp (-(2 * t)) ≤ ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ^ (-2 : ℤ) := by
      intro τ i
      obtain ⟨h0, h1⟩ := hd τ i.castSucc
      have hu : 0 < ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ := norm_pos_iff.2 h0
      have hu' : ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ≤ Real.exp t := by
        calc ‖dmin X.Gm (cpt X x z) τ i.castSucc‖
            = Real.exp (Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖) := (Real.exp_log hu).symm
          _ ≤ Real.exp t := Real.exp_le_exp.2 (abs_le.1 h1).2
      rw [zpow_neg, zpow_two, Real.exp_neg, two_mul, Real.exp_add]
      exact inv_anti₀ (by positivity) (mul_le_mul hu' hu' hu.le (Real.exp_pos _).le)
    have hprod : Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r) ≤ densF X x z := by
      unfold densF
      calc Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r)
          = ∏ τ : X.Ψ, ∏ i : Fin r, Real.exp (-(2 * t)) := by
            rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
              Fintype.card_fin, ← pow_mul, Nat.mul_comm (Fintype.card X.Ψ)]
        _ ≤ _ := Finset.prod_le_prod (fun τ _ => by positivity) (fun τ _ =>
            Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hfac τ i))
    refine le_trans ?_ hprod
    rw [← Real.exp_nat_mul, QuadraticCoefficientForms.card_Psi X]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have e1 : (fdeg E : ℝ) * r * -(2 * t) = -(18 * ((r : ℝ) ^ 3 * δ * fdeg E)) := by rw [ht]; ring
    have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * w := by positivity
    rw [e1]
    nlinarith

end GlobalTheory.ChartNearOne
