import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadCharacterBoundStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValidStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem small_prime_lt (eps C8 : ℝ) (he : 0 < eps) (h8 : 1 ≤ C8) : ∃ x0 : ℝ, ∀ (s : Scale) (N q0 : ℝ), s.eps = eps → x0 ≤ s.x →
    0 < N → Real.log N ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 → q0 ≤ N ^ C8 → q0 < s.X' := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.scale_poly_comparison eps (2 * C8) (1 / 2) he (by norm_num)
  refine ⟨x0, fun s N q0 hs hx hN hlog hq => ?_⟩
  have h := (hx0 s hs hx).2.2.2.2.2.2
  have hx1 := s.one_lt_alt
  have h1 : 1 ≤ s.x ^ (2 * C8) := Real.one_le_rpow hx1.le (by linarith)
  have hX : 1 < s.X' := Real.one_lt_exp_iff.2 (Real.rpow_pos_of_pos (by linarith) _)
  have h2 : s.X' ^ (1 / 2 : ℝ) < s.X' := by
    calc s.X' ^ (1 / 2 : ℝ) < s.X' ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
      _ = s.X' := Real.rpow_one _
  have h3 : N ^ C8 ≤ Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ C8)
    linarith
  have h4 : Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
      Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ (2 * C8) :=
    le_mul_of_one_le_right (Real.exp_pos _).le h1
  linarith

theorem X'_le_b (s : Scale) : s.X' ≤ s.b := by
  have := s.eps_pos
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith))

theorem has_withDuty_and_chosen {Q : PtProp} {C : FC} {cD ch C8 C5 c6 Cb Cdg : ℝ} (p : Pt C) {R : Ranks} {H : Host R} {q0 : ℕ}
    {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hC : Std C) (hT : H.CT2 = C.CT2)
    (hH : HostGood p.L.sc C8 C5 c6 Cb H q0) (hq : (q0 : ℝ) < p.L.sc.X')
    (h0 : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) (hW : WOK p.L.sc cD ch C.GK H a b)
    (hV : Val C cD ch p.L) (hF : p.From H a b c u0) (hI : CanonInst p.ta.Gx) (hQ : p.Has Q)
    (h1 : ChProviso_at p.L 3) (h2 : p.L.TuGe)
    (h3 : ∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) (h4 : FactDGam p.D Cdg) :
    p.Has (withDuty Q) ∧ p.Chosen C5 c6 Cb Cdg := by
  have hw := GlobalTheory.T.weight_requirement_of_valid C cD ch p R H a b M c u0 hC hV hF hI h0 hW
  obtain ⟨hv, -, hT2, -, hQD, hBox, -, hThin, hBad, -, -, -, ⟨hp, hmod, -, hne, hne'⟩, hlev⟩ := hH
  have hb := GlobalTheory.T.bad_character_bound C p R H a b M c u0 Cb hF hI hBad
  have hBW := hF.boxesW hBox
  have hRW := hF.qdRowsW hBox
  have hTh := hF.chThin hThin
  have eQS := hF.QS_eq
  obtain ⟨eR, -, eT2, eq, ed, eg, ep, ep', hsub, -⟩ := hF
  subst eR
  have hq0 : (0 : ℝ) < q0 := by exact_mod_cast hp.pos
  have hXb := X'_le_b p.L.sc
  refine ⟨⟨hQ, hw, hBW, hRW, q0, hsub (by rw [hlev]; simp), hp, ?_, ?_, hq, ?_, ?_, ?_⟩, ?_, hb, ?_, hTh, h1, h2, h3, h4⟩
  · rw [eQS, eq, ed]; exact hmod
  · rw [Real.log_le_iff_le_exp hq0]
    exact hq.le.trans hXb
  · rw [ep]; exact hne
  · rw [ep']; exact hne'
  · intro i hi
    have hg := (hv.2.2.2.2.1 i).1
    rw [← eg, ← hi] at hg
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  · unfold ThickSetLowerBound Host.secondSet_card_lower_bound
    rw [eT2, hV.secondConstant_eq, hV.host.2.2.2.2.2.1, ← hT, ← hv.2.2.2.2.2.1]
    exact hT2
  · unfold ChQD_at
    rw [eq, ed]
    exact hQD

end GlobalTheory.EX
