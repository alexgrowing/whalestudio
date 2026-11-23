import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetAllComponentsMax
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBoundsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHostStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardComponentsLeAtGoodEmbeddingStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_net_max_at_goodEmb : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ NN : Finset (FPt (T.U j σ).X), NN.Nonempty ∧ (∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∃ p ∈ NN, supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) P ≤ 4 * ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w) w.n p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h hG large₂ j hj w hw hL hrn hf σ hσ

  have hne0 : Nonempty (T.U j σ).Comp := ⟨(T.dict j σ 1).1⟩
  obtain ⟨-, hlrd, hd, hcc, hlf, -, -, -, hn⟩ := id hw
  obtain ⟨-, -, -, -, -, hfdeg, hdE, -, hfr, hf1, -, -, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hlrd hd hcc
  obtain ⟨e, M, wg, hM1, hMl, hwg, hwgl, -, hk⟩ := GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T h hG large₂ j hj w hw hL hrn σ hσ
  have hcard := GlobalTheory.T.log_card_components_le_at_good_embedding D T h large₂ j hj w hw hL hrn hf σ hσ
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := by linarith
  have hr1 : 1 ≤ D.R.r := le_trans hf1 hfr
  have hF1 : (1 : ℝ) ≤ (fdeg D.host.E : ℝ) := by rw [hfdeg]; exact_mod_cast hf1
  have hZ : Zb D large₂ = (fdeg D.host.E : ℝ) * D.R.r * large₂.sc.L := by rw [hfdeg]; rfl

  have hlogr : Real.log (D.R.r : ℝ) ≤ large₂.sc.L := by
    refine le_trans (Real.log_le_log (by exact_mod_cast hr1) (by exact_mod_cast hrn)) hn
  have hlogf : Real.log (fdeg D.host.E : ℝ) ≤ 2 * large₂.sc.L := by rw [hfdeg]; exact hlf
  obtain ⟨NN, hne, hP, hlog⟩ :=
    GlobalTheory.NetMax.exists_net_all_components_max D.host.E D.R.r (T.U j σ).Comp (fun k => (e k).toX)
      (laU (T.U j σ) (wtA w) w.n) M wg large₂.sc.L hr1 hL1 hM1 hwg (fun k => (hk k).1) (fun k => (hk k).2.1)
      hlogf hlogr hMl hwgl hdE
      (fun k => ⟨(hk k).2.2.1, le_trans (hk k).2.2.2.1 (by nlinarith),
        le_trans (hk k).2.2.2.2.1 (by nlinarith), le_trans (hk k).2.2.2.2.2.1 (by nlinarith)⟩)
      (by rw [← hZ]; exact hcard)
  refine ⟨NN, hne, hP, ?_⟩
  rw [hZ]
  exact hlog

end GlobalTheory.RunIn
