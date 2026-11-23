import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunIsotropicMeanUnipotentInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermDependsOnlyOnIsotropicMeansStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TermInvProof

theorem termInv : ∀ D : D7, TermInv D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y s I hI hY n hn f₁ f₂ hf₁ hf₂
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne (D := D) (m := s) (n := V.rank)
  exact GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means D ψ hS.weil.std V W μ 𝓕 hS.covol Y (fr Y) (hS.frame Y) s I hI hY ν 𝓨 hν _ _ f₂
    (hS.weil.om_pres _ f₁ hf₁) hf₁ hf₂
    (fun x hx => GlobalTheory.T.thetaFun_isotropic_mean_unipotent_invariant D ψ V W χV χW om hS.weil s I hI ν 𝓨 hν n hn f₁ hf₁ x hx)

end GlobalTheory.TermInvProof

end
