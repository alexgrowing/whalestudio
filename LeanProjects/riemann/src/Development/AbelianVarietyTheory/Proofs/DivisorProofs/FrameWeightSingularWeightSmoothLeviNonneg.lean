import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothEtaleOfSmoothInChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtPsiOfNotMemZeroSetStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s hs δ hlevi U z β hz hβ hU
  have hJ := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hz
  have hW := GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph n Y ι La A E U β (jdet A z) hz.isOpen hβ hJ
  have hP : ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source →
      ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i x) :=
    fun x hx i hi => GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet n Y ι La A L s hs x (hU x hx) i hi
  have hS := (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A U z hz).2
  refine ⟨hS (GlobalTheory.OTY.TwEst.wt A E β z)
      (fun x hx => ⟨A.pick x, A.mem_pick x, (hW x hx _ (A.mem_pick x)).1⟩),
    hS (psi A L s) (fun x hx => ⟨A.pick x, A.mem_pick x, hP x hx _ (A.mem_pick x)⟩), ?_⟩
  intro α hα
  refine GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A U z hz (fun y => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y)
    (fun x hx => ⟨A.pick x, A.mem_pick x, ?_, fun ξ => ?_⟩)
  · exact (hW x hx _ (A.mem_pick x)).1.add (contDiffAt_const.mul (hP x hx _ (A.mem_pick x)))
  · have hc : ContDiffAt ℝ ∞ ((fun y => α * psi A L s y) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      contDiffAt_const.mul (hP x hx _ (A.mem_pick x))
    exact le_of_le_of_eq (hlevi α hα (A.pick x) x (A.mem_pick x) (hU x hx) ξ)
      ((hW x hx _ (A.mem_pick x)).2 _ hc ξ).symm
