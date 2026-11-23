import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∀ X ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ u f) - Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Datum.dRho (heisO ψ S T) θ τ (X * u) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ' u f) = Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ ∀ (p : GA D S × GA D T) (w : WO S T), HasDerivAt (fun t : ℝ => om (p * (1, oneP θ T τ X t)) f w) (om p (Gn f) w) 0 := by
  first | exact @GlobalTheory.DefLift.Gen.exists_generator | exact GlobalTheory.DefLift.Gen.exists_generator | (intros; apply GlobalTheory.DefLift.Gen.exists_generator <;> assumption)
