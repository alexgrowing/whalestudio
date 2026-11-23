import Mathlib

open Polynomial Module

namespace GlobalTheory.SemisimpleConj

variable {K : Type} [Field K]

noncomputable def actX (K : Type) [Field K] (M : Type) [AddCommGroup M] [Module K[X] M] [Module K M]
    [IsScalarTower K K[X] M] : Module.End K M :=
  Algebra.lsmul K K M (X : K[X])

section
variable {M : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]

instance finiteDimensional_submodule [FiniteDimensional K M] (S : Submodule K[X] M) :
    FiniteDimensional K S :=
  FiniteDimensional.of_injective ((S.subtype).restrictScalars K) Subtype.val_injective

end

section
variable {M N : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]
  [AddCommGroup N] [Module K[X] N] [Module K N] [IsScalarTower K K[X] N]

end

end GlobalTheory.SemisimpleConj
