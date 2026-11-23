import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem ppv_deg_three_eq_deg_two {D : D7} (large₂ : SizeData₂ D) :
    WeightFamilies.PPv D large₂ 1041 3 = WeightFamilies.PPv D large₂ (1041 * zBase large₂) 2 := by
  have h : (0 : ℝ) < zBase large₂ := lt_of_lt_of_le one_pos (WeightFamilies.one_le_zBase large₂)
  unfold WeightFamilies.PPv
  rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add h, Real.rpow_one, mul_assoc]

theorem inputsR_deg_two : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ CL H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨h1, h2, h3, G, Gc, PH, Prw, Pet, Pd, h4, ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩, h6⟩ := h
  have e := ppv_deg_three_eq_deg_two large₂
  refine ⟨h1, ?_, h3, G, Gc, PH, Prw, Pet, Pd, h4, ⟨f1, f2, f3, ?_, f5, f6, f7, f8, f9, f10, f11, f12⟩, h6⟩
  · intro F σ
    have := h2 F σ
    change _ ≤ Real.exp (WeightFamilies.PPv D large₂ 1041 3 * _) * _ at this
    rw [e] at this
    exact this
  · have := f4
    change WeightFamilies.PPv D large₂ 1041 3 * _ ≤ _ at this
    rw [e] at this
    exact this

end GlobalTheory.FinalJoin
