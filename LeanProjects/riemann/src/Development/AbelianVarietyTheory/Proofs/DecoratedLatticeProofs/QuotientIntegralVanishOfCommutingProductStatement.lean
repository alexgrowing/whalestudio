import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProduct
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  first | exact @GlobalTheory.CommProd.quot_vanish_of_prod | exact GlobalTheory.CommProd.quot_vanish_of_prod | (intros; apply GlobalTheory.CommProd.quot_vanish_of_prod <;> assumption)
