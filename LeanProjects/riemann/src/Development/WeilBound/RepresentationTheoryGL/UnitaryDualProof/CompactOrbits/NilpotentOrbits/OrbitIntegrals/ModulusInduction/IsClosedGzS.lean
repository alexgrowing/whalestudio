import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem totDisc : TotallyDisconnectedSpace k := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

def SpT (k : Type) [Field k] (n : ℕ) : Type := Sp k n

instance : TopologicalSpace (SpT k n) := inferInstanceAs (TopologicalSpace (Sp k n))

theorem t2Sp : T2Space (SpT k n) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  exact inferInstanceAs (T2Space (Matrix (Fin n) (Fin n) k × (Fin n → k)))

theorem lcSp : LocallyCompactSpace (SpT k n) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  exact inferInstanceAs (LocallyCompactSpace (Matrix (Fin n) (Fin n) k × (Fin n → k)))

theorem tdSp : TotallyDisconnectedSpace (SpT k n) := by
  have : TotallyDisconnectedSpace k := totDisc
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact inferInstanceAs (TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k × (Fin n → k)))

instance actGL : MulAction (GL (Fin n) k) (SpT k n) where
  smul g p := (act g p : Sp k n)
  one_smul := act_one (k := k)
  mul_smul := act_mul (k := k)

theorem contSMul : ContinuousSMul (GL (Fin n) k) (SpT k n) := by
  refine ⟨?_⟩
  show Continuous fun p : GL (Fin n) k × (Matrix (Fin n) (Fin n) k × (Fin n → k)) => act p.1 p.2
  unfold act
  refine Continuous.prodMk ?_ ?_
  · exact ((Units.continuous_val.comp continuous_fst).matrix_mul
      (continuous_fst.comp continuous_snd)).matrix_mul (Units.continuous_coe_inv.comp continuous_fst)
  · exact (Units.continuous_val.comp continuous_fst).matrix_mulVec (continuous_snd.comp continuous_snd)

theorem isClosed_GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (GzS Z : Set (GL (Fin n) k)) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have e : (GzS Z : Set (GL (Fin n) k)) =
      ⋂ a ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g
    simp [GzS, Gz]
  rw [e]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val)
    (Units.continuous_val.matrix_mul continuous_const)

theorem lcH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : LocallyCompactSpace (GzS Z) :=
  (isClosed_GzS Z).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem tdGL : TotallyDisconnectedSpace (GL (Fin n) k) := by
  have : TotallyDisconnectedSpace k := totDisc
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  refine ⟨fun t _ ht => ?_⟩
  have h := isTotallyDisconnected_of_totallyDisconnectedSpace (Units.val '' t) (Units.val '' t)
    subset_rfl (ht.image _ Units.continuous_val.continuousOn)
  intro x hx y hy
  exact Units.val_injective (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

theorem tdH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : TotallyDisconnectedSpace (GzS Z) := by
  have := tdGL (k := k) (n := n)
  infer_instance

theorem scH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SigmaCompactSpace (GzS Z) := by
  have := lcH Z
  have := GlobalTheory.SplitWeil.secondCountable k
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) k) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : SecondCountableTopology (GzS Z) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

theorem contSMulH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : ContinuousSMul (GzS Z) (SpT k n) := by
  have := contSMul (k := k) (n := n)
  refine ⟨?_⟩
  show Continuous fun p : GzS Z × SpT k n => (p.1 : GL (Fin n) k) • p.2
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

theorem isOpen_UU : IsOpen (UU : Set (Sp k n)) := by
  have := GlobalTheory.SplitWeil.t2Space k
  exact isOpen_compl_singleton.preimage continuous_snd

open scoped Pointwise in

theorem relIndex_ne_zero {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {J A : Subgroup H}
    (hJ : IsCompact (J : Set H)) (hA : IsOpen (A : Set H)) : A.relIndex J ≠ 0 := by
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  have hA' : IsOpen ((A.subgroupOf J : Subgroup J) : Set J) := by
    rw [Subgroup.coe_subgroupOf]
    exact hA.preimage continuous_subtype_val
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun g : J => g • ((A.subgroupOf J : Subgroup J) : Set J))
    (fun g => by
      rw [← Set.image_smul]
      exact (Homeomorph.mulLeft g).isOpenMap _ hA')
    (fun x _ => Set.mem_iUnion.2 ⟨x, ⟨1, (A.subgroupOf J).one_mem, mul_one x⟩⟩)
  have hc : ⋃ i ∈ t, (fun g : J => g) i • ((A.subgroupOf J : Subgroup J) : Set J) = Set.univ :=
    Set.eq_univ_of_univ_subset ht
  have := Subgroup.finiteIndex_of_leftCoset_cover_const hc
  exact Subgroup.finiteIndex_iff.mp this

end PositivityTheory.RgUd.T.Nil.Orb.BStep
