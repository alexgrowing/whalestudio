import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.ConstantTermL2

theorem main : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule D.host.E V.V) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (F : DividedPowerChartLift V μ), LocallyIntegrable (constTerm (.single hW) (lift (GQ V) F)) μ ∧ (∀ u ∈ NA (.single hW), (fun g => constTerm (.single hW) (lift (GQ V) F) (u * g)) =ᵐ[μ] constTerm (.single hW) (lift (GQ V) F)) ∧ ∀ f : GA D V → ℂ, Continuous f → HasCompactSupport f → ∀ x, constTerm (.single hW) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) x = ∫ y, f (x⁻¹ * y) * constTerm (.single hW) (lift (GQ V) F) y ∂μ := by
  intro D V μ _ _ W hW F
  have hc := cocompact_single hW
  have hl := leftInv_lift (Γ := GQ V) F
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have hi := GlobalTheory.CuspAE.locallyIntegrable_lift (Γ := GQ V) (μ := μ) F
  refine ⟨GlobalTheory.CuspAE.locallyIntegrable_constTermOn hc hl hm hi, fun u hu => .of_forall fun g =>
    hc.constTermOn_mul_left hl hu g, fun f hf hs x => ?_⟩
  have e1 : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq (μ := μ) f _ x).symm
  rw [e1, ← convR_eq (μ := μ)]
  exact GlobalTheory.CuspAE.constTermOn_convR hc hl hm hi hf hs x

end GlobalTheory.ConstantTermL2
