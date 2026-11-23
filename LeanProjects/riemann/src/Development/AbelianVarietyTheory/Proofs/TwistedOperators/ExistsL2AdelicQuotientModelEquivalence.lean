import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
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

namespace GlobalTheory.TrModel

theorem exists_model : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∃ (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕))) (e : DividedPowerChartLift V μ ≃ₗᵢ[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕)), GlobalTheory.HolDict.FinPair V μ 𝓕 ∧ GlobalTheory.HolDict.IsReg V μ 𝓕 ρ ∧ (∀ g F, e (RG V μ g F) = ρ g (e F)) ∧ ∀ F ψ, GlobalTheory.HolDict.Repr V μ 𝓕 (e F) ψ ↔ lift (GQ V) F =ᵐ[μ] ψ := by
  intro D V μ _ _
  refine ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), RG V μ, LinearIsometryEquiv.refl ℂ _, ?_, ?_, fun g F => rfl, fun F ψ => Iff.rfl⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ,
      (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ _ inferInstance
        (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ)).ne⟩
  · exact ⟨fun g F => GlobalTheory.AutomorphicL2Unitary.lift_R g F, fun g F => GlobalTheory.AutomorphicL2Unitary.norm_R g F,
      fun F => (isUnitaryRep_RG (V := V) (μ := μ)).continuous_apply F⟩

end GlobalTheory.TrModel
