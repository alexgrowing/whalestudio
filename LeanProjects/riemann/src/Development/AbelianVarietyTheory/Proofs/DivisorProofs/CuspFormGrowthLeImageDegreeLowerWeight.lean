import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentFunctionFieldFgStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsRatioOnComponentOfBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBoundStatement

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem growthOn_le_compDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  intro E _ _ _ H Dw l Xo c r U hU Z G G' hG hG' hfin hB hM
  rcases eq_or_ne (growthOn U Z G') 0 with h0 | h0
  · rw [h0]; exact bot_le
  obtain ⟨a, θ, ha, hθ, hmul⟩ := hM
  haveI := GlobalTheory.DegTop.finiteDimensional_of_growthOn (U := U) (Z := Z) hG hfin
  have hR := GlobalTheory.T.cuspFormsRatioOnComponent_of_birational E H Dw l Xo c r U Z G hB
  have hFG := GlobalTheory.T.flagSpaceComponent_functionField_fg E H Dw l Xo c r U hU Z
  set ev := genPoint Z (cuspOn U Z G) with hev
  let S : ℕ → Submodule c.F (Om Z) := fun k =>
    if k = 0 then ⊥ else (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k))
  have h1 := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.1 c.F _ _ ev (dimFlag Dw) a ha S (by
    intro k t ht
    by_cases hk : k = 0
    · simp only [S, hk, if_true, Submodule.mem_bot] at ht
      subst ht
      refine ⟨?_, ⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩⟩
      rw [IsIntDeg, map_zero, mul_zero]
      exact isIntegral_zero
    · simp only [S, hk, if_false] at ht
      obtain ⟨f, hf, rfl⟩ := ht
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
      obtain ⟨hc, hv⟩ := hmul k hk1 f hf
      exact ⟨GlobalTheory.T.isIntegralInConeDegree_of_valuativeBound c.F _ _ ev inferInstance inferInstance hFG _ _ hv, hR _ _ hc⟩)
  have hθk : ∀ k : ℕ, genVal Z (θ ^ k) ≠ 0 := fun k => by rw [map_pow]; exact pow_ne_zero _ hθ
  have h2 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) ≤
      growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (S k))) :=
    GlobalTheory.DegTop.growth_mono _ fun k hk => by
      have hk0 : k ≠ 0 := by omega
      show _ ≤ Cardinal.toENat (Module.rank c.F (S k))
      have hS : S k = (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k)) := if_neg hk0
      rw [hS, GlobalTheory.DegTop.rank_map_mul (U := U) (G := (a * k) • G') (hθk k)]
  have hmulG : ∀ G₀ : WTZ E, growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G₀)))) =
      growthOn U Z (a • G₀) := fun G₀ => by
    rw [growthOn]
    congr 1
    funext k
    rw [mul_nsmul]
  have h3 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) =
      (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' := by
    rw [hmulG, GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G' hG' a ha]
  have h4 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≤ (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
    rw [← GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G hG a ha, ← hmulG]
    exact GlobalTheory.DegTop.growth_mono _ fun k hk => GlobalTheory.DegTop.hilb_le hG (Nat.mul_pos ha hk)
  have haD0 : (a : ℝ≥0∞) ^ dimFlag Dw ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have haDT : (a : ℝ≥0∞) ^ dimFlag Dw ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have hlow : (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' ≤ growth (dimFlag Dw) (fun k => hilb ev (a * k)) :=
    h3 ▸ h2.trans h1
  have hne0 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ 0 :=
    ne_bot_of_le_ne_bot (mul_ne_zero haD0 h0) hlow
  have hneT : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top haDT hfin) h4
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.1 c.F _ _ ev (dimFlag Dw) a ha hne0 hneT
  rw [GlobalTheory.T.cone_degree_growth_chowForm_integrality.1 c.F _ _ ev (dimFlag Dw) a ha δ hδ] at hlow
  rw [compDeg, ← hev, hδ.imageDeg_eq]
  first | exact (ENNReal.mul_le_mul_iff_right haD0 haDT).1 hlow | exact (ENNReal.mul_le_mul_iff_left haD0 haDT).1 hlow

end GlobalTheory.DegVal
