import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DivisorHalfGenerationOfCover
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
section
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
theorem divisor_half_generated_on_cover_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  intro _ h2 _ _
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
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
end
section
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_half_generated_of_covers : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  first | exact @_root_.GlobalTheory.HalfCover.divisor_half_generated_on_cover_alt | exact _root_.GlobalTheory.HalfCover.divisor_half_generated_on_cover_alt | (intros; apply _root_.GlobalTheory.HalfCover.divisor_half_generated_on_cover_alt <;> assumption)
end
end
