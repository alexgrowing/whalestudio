import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameGeneratorResidual
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionTrivialOnWildInertia
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.ResidualTame
namespace GlobalTheory.RowWildTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.RowWildTame
namespace GlobalTheory.RowTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem tameGenerator_residual_alt_alt (D : D7) (h1 : GlobalTheory.RowCopy.RbarTie D) (h2 : GlobalTheory.RowTie.IotaRed D)
    (h3 : _root_.UpperTheory.GalS.LabTameS D.nd D.naut) (h4 : _root_.UpperTheory.GalS.RowRepAtGN D) :
    GlobalTheory.RowCopy.JointOccurrenceCondition D := by
  intro σ k v _ _ i hl hne hg
  refine ⟨_root_.GlobalTheory.ResidualTame.cpAt' D h1 h2 h3 h4 σ k v i hl hne hg, ?_⟩
  obtain ⟨φ, hI, hW⟩ := GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild _ _ _ D.nd D.naut k v _ (D.ntypes.tg_mem k v)
  refine ⟨φ, ?_⟩
  have h := _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN D h1 h3 h4 σ k v i hl hne hg _ hI hW
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h
  exact h
end GlobalTheory.RowTie
end
end
