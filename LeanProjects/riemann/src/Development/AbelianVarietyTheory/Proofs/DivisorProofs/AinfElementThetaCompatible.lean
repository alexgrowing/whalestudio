import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem inA_mem_nonZeroDivisors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ a : Ainf p O, a ≠ 0 → (inA a : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ a ha
  haveI : IsDomain (Ainf p O) := (GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε).1
  haveI : Module.IsTorsionFree ℤ_[p] Λ := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free (Ainf p O) (RL p O Λ) := inferInstance
  haveI : Module.IsTorsionFree (Ainf p O) (RL p O Λ) := inferInstance
  have key : ∀ r : RL p O Λ, inA a * r = 0 → r = 0 := by
    intro r hr
    rw [← Algebra.smul_def] at hr
    exact (smul_eq_zero.mp hr).resolve_left ha
  refine mem_nonZeroDivisors_iff_right.mpr fun r hr => key r ?_
  rwa [mul_comm]

end GlobalTheory.DetInv
