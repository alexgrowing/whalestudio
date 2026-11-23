import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.CompanionTheory.AutCover

open scoped Pointwise

theorem integrable_descend_of_cover : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (S : Set (GA D V)),
    MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → ∀ φ : GA D V → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ →
      Measurable φ → IntegrableOn φ S μ → Integrable (descend (GQ V) φ) (autMeasure V μ) := by
  intro D V μ _ S hS hcov φ hinv hφ hint
  have hmeas : AEStronglyMeasurable (descend (GQ V) φ) (autMeasure V μ) :=
    (GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift).2 (by
      rw [hinv.lift_descend]
      exact hφ.aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  have hfin : ∫⁻ g in S, ‖φ g‖ₑ ∂μ < ⊤ := hint.2
  have hmf : AEMeasurable (S.indicator fun g => ‖φ g‖ₑ) μ := (hφ.enorm.indicator hS).aemeasurable
  have key := GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := GQ V) (μ := μ) hmf
  rw [lintegral_indicator hS] at key
  show ∫⁻ q, ‖descend (GQ V) φ q‖ₑ ∂(autMeasure V μ) < ⊤
  refine lt_of_le_of_lt ?_ hfin
  rw [key]
  apply lintegral_mono
  intro q
  obtain ⟨γ, hγ, s, hs, hq⟩ := hcov q.out
  have e : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out = s := by
    show γ⁻¹ * q.out = s
    rw [hq, inv_mul_cancel_left]
  have hmem : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out ∈ S := by
    rw [e]
    exact hs
  have h1 : S.indicator (fun g => ‖φ g‖ₑ) ((((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out) = ‖φ q.out‖ₑ := by
    rw [Set.indicator_of_mem hmem, hinv _ (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V)).2]
  show ‖φ q.out‖ₑ ≤ _
  rw [← h1]
  exact ENNReal.le_tsum (f := fun γ : GQ V => S.indicator (fun g => ‖φ g‖ₑ) ((γ : GA D V) * q.out)) _

end GlobalTheory.CompanionTheory.AutCover
