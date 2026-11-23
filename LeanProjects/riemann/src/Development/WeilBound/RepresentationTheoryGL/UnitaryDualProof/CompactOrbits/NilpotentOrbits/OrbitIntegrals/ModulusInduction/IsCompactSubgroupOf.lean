import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.PieceCount

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem stab_subgroupOf {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n) :
    (stab Z p).subgroupOf (GzS Z) = stabilizer (GzS Z) (toT p) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨x.2, h⟩

theorem inf_subgroupOf' {G : Type*} [Group G] (A B G' : Subgroup G) :
    (A ⊓ B).subgroupOf G' = A.subgroupOf G' ⊓ B.subgroupOf G' := by
  ext x
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

theorem relIndex_H {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n)
    {K L : Subgroup (GL (Fin n) k)} (hKG : K ≤ GzS Z) :
    ((L ⊓ stab Z p).relIndex (K ⊓ stab Z p) = ((L.subgroupOf (GzS Z)) ⊓ stabilizer (GzS Z) (toT p)).relIndex
      ((K.subgroupOf (GzS Z)) ⊓ stabilizer (GzS Z) (toT p))) ∧
    L.relIndex K = (L.subgroupOf (GzS Z)).relIndex (K.subgroupOf (GzS Z)) := by
  refine ⟨?_, (Subgroup.relIndex_subgroupOf hKG).symm⟩
  rw [← stab_subgroupOf, ← inf_subgroupOf', ← inf_subgroupOf',
    Subgroup.relIndex_subgroupOf (inf_le_left.trans hKG)]

theorem isCompact_subgroupOf {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {K : Subgroup (GL (Fin n) k)}
    (hKG : K ≤ GzS Z) (hKc : IsCompact (K : Set (GL (Fin n) k))) : IsCompact ((K.subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [Subtype.isCompact_iff]
  convert hKc using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKG hx⟩, hx, rfl⟩

end PositivityTheory.RgUd.T.Nil.Orb.BStep
