import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular : ∀ (D : D7) (V : HSp D), IsClosed (GinfC V : Set (GA D V)) ∧ IsClosed (GfC V : Set (GA D V)) ∧ (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a) ∧ (∃ e : (GinfC V × GfC V) ≃ₜ GA D V, ∀ p, e p = p.1 * p.2) ∧ (∀ μ : Measure (GfC V), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ((∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ (∀ μ : Measure (jacGrp d), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o) ∧ (∀ μ : Measure (besGrp d o), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant := by
  first | exact @GlobalTheory.AdelicSplit.adelic_split | exact GlobalTheory.AdelicSplit.adelic_split | (intros; apply GlobalTheory.AdelicSplit.adelic_split <;> assumption)
