import Mathlib

noncomputable section

namespace PI.FinExtTop

structure PadicCoeff (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] : Prop where
  ring : IsTopologicalRing O
  compact : CompactSpace O
  t2 : T2Space O
  adic : IsAdic (IsLocalRing.maximalIdeal O)
  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

structure FracTop (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [TopologicalSpace (FractionRing O)] : Prop where
  emb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))

structure IsFGTop (O M : Type) [CommRing O] [TopologicalSpace O] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] : Prop where
  fg : Module.Finite O M
  t2 : T2Space M
  csmul : ContinuousSMul O M

end PI.FinExtTop

namespace PI

open PI.FinExtTop in

def FinExtTop : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'],
    PadicCoeff ℓ O →
    ∃ (_ : Algebra ℤ_[ℓ] O') (_ : IsScalarTower ℤ_[ℓ] O O') (_ : Module.Finite ℤ_[ℓ] O')
      (_ : TopologicalSpace O') (_ : IsModuleTopology O O')
      (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')),
      Function.Injective (algebraMap ℤ_[ℓ] O') ∧ PadicCoeff ℓ O' ∧ FracTop O' ∧
      ∀ (X' d : Type) [Fintype d] [DecidableEq d]
        (R' : Subalgebra O' (X' → Matrix d d (FractionRing O'))), Module.Finite O' R' →
        ∃ (_ : TopologicalSpace R') (_ : IsModuleTopology O' R'),
          IsTopologicalAddGroup R' ∧ ContinuousConstSMul O' R' ∧ ContinuousMul R' ∧
          IsTopologicalRing R' ∧ IsFGTop O' R'

end PI
