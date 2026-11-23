import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyReductionGoodPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReductionTrivialOnWildInertiaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem tameGenerator_residual (D : D7) (h1 : GlobalTheory.RowCopy.RbarTie D) (h2 : GlobalTheory.RowTie.IotaRed D)
    (h3 : GlobalTheory.RowTie.LabTame D.nd D.naut) (h4 : GlobalTheory.RowTie.RowRepAtG D) :
    GlobalTheory.RowCopy.JointOccurrenceCondition D := by
  intro σ k v _ _ i hl hne hg
  refine ⟨GlobalTheory.T.charpoly_reduction_good_prime D h1 h2 h4 σ k v i hl hne hg, ?_⟩
  obtain ⟨φ, hI, hW⟩ := GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild _ _ _ D.nd D.naut k v _ (D.ntypes.tg_mem k v)
  refine ⟨φ, ?_⟩
  have h := GlobalTheory.T.reduction_trivial_on_wild_inertia D h1 h3 h4 σ k v i hl hne hg _ hI hW
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h
  exact h

end GlobalTheory.RowTie
