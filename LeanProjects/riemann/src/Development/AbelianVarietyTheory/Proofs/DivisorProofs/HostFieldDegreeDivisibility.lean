import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfCover

theorem half_gen_on_cover : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  intro _ h2 _ _
  unfold Covers Lifts
  refine Formalism.MainNotions.Closed.imp h2 ?_
  intro eps Fm CH _ _
  refine ⟨0, le_rfl, 0, fun x hx _ ι p _ i hi Y hY => ?_⟩
  letI := p.T.Q.H.starRing
  have hL := p.fw.laws
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split (Fm.D x ι) p.T.toCore hL.toLawsM (Fm.ex x hx ι).errX
  have hM : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := hL.pins.2.1.1
  have hlev := hY.1.lev.1
  have hq := (hL.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, by omega⟩).2.1
  refine ⟨α, by rw [hα1, hM], ?_, ?_, ?_⟩
  · rw [hlev.2.1, ← hM]
    exact dvd_mul_right _ _
  · rw [hlev.2.2.2.1, ← hα2]
    exact Ideal.mul_le_left
  · show Module.finrank ℚ (Fm.D x ι).host.E * (p.T.Q.Dw ((i : ℕ) + 1)).q ≤ _
    rw [GlobalTheory.DepthLink.finrank_host, hq]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end GlobalTheory.HalfCover

end
