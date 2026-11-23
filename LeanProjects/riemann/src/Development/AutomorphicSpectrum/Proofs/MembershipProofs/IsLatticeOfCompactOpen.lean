import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.OrderOKOneInert
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIdx

section Lattice

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Lattice

def invT {k : Type} [CommRing k] {β : Type} [Fintype β] [DecidableEq β] (u : GL β k) : GL β k :=
  ⟨((u⁻¹ : GL β k) : Matrix β β k)ᵀ, (u : Matrix β β k)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

def swapAlg (k : Type) [CommRing k] : (k × k) ≃ₐ[k] k × k :=
  { (RingEquiv.prodComm : k × k ≃+* k × k) with commutes' := fun _ => rfl }

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {E : Type} [CommRing E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Split

end GlobalTheory.CompanionTheory.SplitIdx
