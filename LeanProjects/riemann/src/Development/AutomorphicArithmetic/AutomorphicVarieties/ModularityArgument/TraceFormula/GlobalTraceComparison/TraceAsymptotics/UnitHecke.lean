import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLTwConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem unitHecke : UnitHecke := by
  intro E _ _ _ n a b w
  have hG : ∀ m : ℕ, IsOpen (KGL w m : Set (GLw m w)) ∧ IsCompact (KGL w m : Set (GLw m w)) :=
    fun m => GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w m
  have hKLo : IsOpen (KL n w : Set (UL n w)) := (hG n).1.preimage continuous_subtype_val
  have hKLc : IsCompact (KL n w : Set (UL n w)) := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨hKLo, ⟨?_, ?_⟩, (hG n).1, (hG n).2, ?_, ?_, ?_⟩
  · have hcl : IsClosed (KL n w : Set (UL n w)) := Subgroup.isClosed_of_isOpen _ hKLo
    refine hKLc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcl)
    exact Set.support_indicator_subset
  · intro k hk x
    constructor
    · simp [Set.indicator, Subgroup.mul_mem_cancel_left _ hk]
    · simp [Set.indicator, Subgroup.mul_mem_cancel_right _ hk]
  · exact (hG a).1.prod (hG b).1
  · exact (hG a).2.prod (hG b).2
  · intro k hk
    unfold thL
    split_ifs
    · exact hk
    · exact GlobalTheory.CompanionTheory.IwFacts.thetaGL_mem_KGL w n hk

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
