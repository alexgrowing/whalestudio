import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeafStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPrimeWeightHypothesesOfDepthParametersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParametersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegreeStatement

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem numOf_sizes_le (D : D7) (L : SizeData₂ D) (hk : (1 : ℝ) ≤ D.R.k) (hm : (1 : ℝ) ≤ D.R.m) :
    (numOf D L).Sc + (numOf D L).eta ≤ L.Sc + L.etaSz := by
  have hS := L.Sc_pos
  have hE := L.Sc_eq
  have he := L.etaSz_pos
  have hDel : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have h1 : (numOf D L).Sc ≤ L.Sc := by
    show (D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)) ≤ L.Sc
    rw [hE]
    have := Nat.floor_le hDel
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (numOf D L).eta ≤ L.etaSz := by
    show (D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ) ≤ L.etaSz
    have hm0 : (0 : ℝ) < D.R.m := by linarith
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    have h0 : 0 ≤ LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; positivity
    rw [e]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le h0) hm0.le
  linarith

theorem card_RPl (R : Ranks) : Fintype.card (RPl R) = R.f := by
  simp [RPl, Ranks.f, Ranks.n, R.card_A]

set_option maxHeartbeats 1000000 in

theorem leafGood_run : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.depthTable_goodPrimeLeaf 100 (by norm_num)
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm R hPk hC hPg hSz hCn hx5 hx hkb tF
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe Scale.b Scale.L
    rw [R.x_eq, R.eps_eq]
  have hL : O.L = L.sc.L := by
    unfold OnObj.L
    rw [hb, Scale.b, Real.log_exp]
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hk1 : (1 : ℝ) ≤ D.R.k := R.k_eq ▸ hPg.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := R.m_eq ▸ hPg.2.2.1
  have hf8 : (8 : ℝ) ≤ D.R.f := R.f_eq ▸ hPg.2.2.2.1
  have hlog : Real.log D.R.k ≤ L.sc.L := by
    have := hSz.2.2.2.2.2.2.1
    rwa [R.k_eq, hL] at this
  refine hC0 D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι Nm (numOf D L)
    (fun z => DV.tauEmb D (plOf D z)) hC R.E_eq R.σ_eq R.T_eq ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
    (piSplit_depDataOf ..) (levelQ_depDataOf _ _ _ _ _ _ _ _ _ hT) R.star_eq
    (fun j => (GlobalTheory.T.exists_integral_chart_integral_framed_point _ _ _ _ _ _).2.1 R.star_eq) hPk (GlobalTheory.T.realPlaces_match_cmTypeFrobenius D L T hT.pins) (fun j => ?_) ?_ hPg tF
    ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
  · have hj := R.inR j
    have hd := hT.pins.2.2.2 _ hj
    refine ⟨hj.1, hj.2, hd.1, hd.2.1, fun τ i i' h => (dom_wtA (lR Tp hK (ι j))).1 τ h, ?_⟩
    rw [hb, hL]
    exact GlobalTheory.T.goodPrimeWeightHypotheses_of_depthParameters D L Pm Tp hK T hT.pins hCn hx5 hx hkb hlog _ hj
  · refine ⟨R.k_eq, R.m_eq, R.f_eq, ?_, R.depthNumbers_threshold_eq, R.th_eq, R.ad_eq, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · unfold OnObj.Se
      rw [R.Sc_eq, R.eta_eq]
      exact numOf_sizes_le D L hk1 hm1
    · rw [R.wt_eq]
      have h := (GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK (ι j) (R.inR j) hx hkb).2
      calc (∑ z, (numOf D L).w (ι j) z) ≤ ∑ _z : RPl D.R, 2 * L.sc.b := Finset.sum_le_sum fun z _ => (h z).2
        _ = 2 * (D.R.f : ℝ) * L.sc.b := by
          rw [Finset.sum_const, Finset.card_univ, card_RPl, nsmul_eq_mul]; ring
    · rw [R.wt_eq, hb]; nlinarith
    · have h := (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hT.pins (ι j) (R.inR j) (lR Tp hK (ι j))).1
      have h2 := R.DF_ge j
      rw [← h] at h2
      exact h2

end GlobalTheory.GoodDepth
