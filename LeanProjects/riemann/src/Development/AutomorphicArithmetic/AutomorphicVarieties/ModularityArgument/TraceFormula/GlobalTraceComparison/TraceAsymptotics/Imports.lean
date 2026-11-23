import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

open GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.adm :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted := by
  intro E _ _ _ n w τ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n τ.V τ.ρ τ.smooth τ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hsmall : FiniteDimensional ℂ (fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w n)) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed τ.ρ U ≤ fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w n) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle
