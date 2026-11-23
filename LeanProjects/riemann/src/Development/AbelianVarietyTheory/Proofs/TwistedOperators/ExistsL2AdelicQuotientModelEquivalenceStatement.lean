import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsL2AdelicQuotientModelEquivalence
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_L2AdelicQuotient_model_equivalence : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∃ (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕))) (e : DividedPowerChartLift V μ ≃ₗᵢ[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕)), GlobalTheory.HolDict.FinPair V μ 𝓕 ∧ GlobalTheory.HolDict.IsReg V μ 𝓕 ρ ∧ (∀ g F, e (RG V μ g F) = ρ g (e F)) ∧ ∀ F ψ, GlobalTheory.HolDict.Repr V μ 𝓕 (e F) ψ ↔ lift (GQ V) F =ᵐ[μ] ψ := by
  first | exact @GlobalTheory.TrModel.exists_model | exact GlobalTheory.TrModel.exists_model | (intros; apply GlobalTheory.TrModel.exists_model <;> assumption)
