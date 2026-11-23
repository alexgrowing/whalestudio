import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTarget
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDistribution_invariant_rationalTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → of (1, γ') (oi (1, γ') f) 0 = f 0 := by
  first | exact @GlobalTheory.RatAut.automorphy_target | exact GlobalTheory.RatAut.automorphy_target | (intros; apply GlobalTheory.RatAut.automorphy_target <;> assumption)
