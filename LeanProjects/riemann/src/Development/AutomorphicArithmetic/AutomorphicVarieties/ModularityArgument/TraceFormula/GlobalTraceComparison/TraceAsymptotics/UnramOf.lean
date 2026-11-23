import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unramOf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.UnramOf := by
  intro E _ _ _ n S π K' hlev w hw hK
  obtain ⟨φ, hφ, h0, hfix⟩ := hlev
  refine ⟨φ, hφ, h0, fun x hx hk => hfix w hw x hx ?_⟩
  have hmem : cLoc w x ∈ UL n w := by
    by_cases hs : IsSplitAt w
    · unfold UL
      rw [if_pos hs]
      trivial
    · exact GlobalTheory.LocInj.cLoc_mem_UL hs x
  refine ⟨⟨cLoc w x, hmem⟩, ?_, rfl⟩
  rw [hK]
  exact Subgroup.mem_subgroupOf.2 hk
