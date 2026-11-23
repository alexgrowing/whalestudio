import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelEisensteinDoubledThetaTermsEqLagrangianInt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' → ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q, ∃ C, IsLagFrame W (e q) C ∧ ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν = lagTerm μ 𝓕 C f₁ f₂ := by
  first | exact @GlobalTheory.SWLagTerms.lagTerms_eq | exact GlobalTheory.SWLagTerms.lagTerms_eq | (intros; apply GlobalTheory.SWLagTerms.lagTerms_eq <;> assumption)
