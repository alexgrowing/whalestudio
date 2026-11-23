import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LinearIndependentOneBeta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem tmul_mem_IntAf (I : AutInst) {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E)
    {a : Formalism.MainNotions.S.Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    x ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
  have h1 : x ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F) ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    refine Subring.subset_closure ?_
    exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  have h2 : (1 : I.E) ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    refine Subring.subset_closure ?_
    exact Or.inr ⟨⟨a, ha⟩, rfl⟩
  have h3 := mul_mem h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

theorem tmul_natCast_mul (I : AutInst) (N : ℕ) (b : I.E) (z : Formalism.MainNotions.S.Af I.F) :
    b ⊗ₜ[I.F] ((N : Formalism.MainNotions.S.Af I.F) * z) = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * (b ⊗ₜ[I.F] z) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]

end PI.InvTopW
