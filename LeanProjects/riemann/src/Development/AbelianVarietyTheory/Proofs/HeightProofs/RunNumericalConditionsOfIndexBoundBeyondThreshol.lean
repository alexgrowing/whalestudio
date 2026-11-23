import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PageRunSqLeRdAndEightLeRank
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ThreeLeDFOfPageRun
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundConstantLePagePolynomialOfRunCondition

set_option autoImplicit false

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem pageOK_of_pageRun_beyond : ∀ Z₀ : ℝ → ℝ → ℝ, ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 ∧ Z₀ H.CA H.CK ≤ zBase large₂ := by
  intro Z₀
  refine ⟨fun a b => max (Z₀ a b) (4 * b), ?_⟩
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP hx
  have hx1 : Z₀ H.CA H.CK ≤ large₂.sc.x := (le_max_left _ _).trans hx
  have hx2 : 4 * H.CK ≤ large₂.sc.x := (le_max_right _ _).trans hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hP.hyp.2.1
  rw [hP.tie.1] at hd
  have hA : 12 ≤ A2 := hP.tie.2.2.2.2.2
  have hC : 1000 ≤ C2 := hd.1
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hxZ : large₂.sc.x ≤ zBase large₂ := hP.hyp.1.1.trans hfr
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have hZP : zBase large₂ ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have h1 : zBase large₂ ≤ zBase large₂ ^ A2 := by
      calc zBase large₂ = zBase large₂ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    exact h1.trans (le_mul_of_one_le_left (by linarith) (by linarith))
  have hf8 : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := hZ1.trans hZP
  have hPP : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f := by
    have h1 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 := by nlinarith
    exact h1.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hfrd := pageRun_sq_le_rd_and_eight_le_rank D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP
  exact ⟨⟨hP.hyp, hP.page, hP.tie, indexBoundConstant_le_pagePolynomial_of_runConditions D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP,
    hfrd.1, hfrd.2, three_le_DF_of_pageRun D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP,
    hx2.trans (hxZ.trans (hZP.trans hPP))⟩, hx1.trans hxZ⟩

end GlobalTheory.FinalJoin
