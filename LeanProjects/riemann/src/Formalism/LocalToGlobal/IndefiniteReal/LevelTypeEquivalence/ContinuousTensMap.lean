import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology

noncomputable section

namespace Formalism.IndefR.Eqv.G5

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance tensIsModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def tensCoordH : R ⊗[F] E ≃ₜ (Fin d → R) :=
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem tensCoordH_apply (y : R ⊗[F] E) (k : Fin d) :
    tensCoordH b R y k = (Algebra.TensorProduct.basis R b).repr y k := rfl

end Coord

end Formalism.IndefR.Eqv.G5
