import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.UnipLevelTopo

theorem isOpen_inf_isCompact : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (J : Subgroup (GL (A ⊕ Fin c) k)) (g : GL (A ⊕ Fin c) k), IsOpen (J : Set (GL (A ⊕ Fin c) k)) → IsCompact (J : Set (GL (A ⊕ Fin c) k)) → IsOpen ((((Cgrp J g).subgroupOf (N k A c 1)) ⊓ ((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1)) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) := by
  intro k _ _ _ _ A _ _ c J g hJo hJc
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj g hJo hJc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : N k A c 1 → GL (A ⊕ Fin c) k) :=
    (GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := A) (c := c) 1).isClosedEmbedding_subtypeVal
  have eC : (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL (A ⊕ Fin c) k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Cgrp, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_sup_right x.2, h⟩⟩
  have eK : (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (KO k (A ⊕ Fin c) : Set (GL (A ⊕ Fin c) k)) := by
    ext x; simp [Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf, eC, eK]
    exact (h1.inter GlobalTheory.SplitFlip.isOpen_KO).preimage continuous_subtype_val
  · rw [eC]; exact hemb.isCompact_preimage h2
  · rw [eK]; exact hemb.isCompact_preimage GlobalTheory.SplitFlip.isCompact_KO

end GlobalTheory.UnipLevelTopo
