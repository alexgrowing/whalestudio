import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.DcosSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.DcosTr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOrdLConjGramDetOfUnitGramAdicCompletion

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT

private theorem exists_unit_ordL_eq_one {E : Type} [Field E] [NumberField E] (w : Pl E) :
    ∃ ϖ : (w.adicCompletion E)ˣ, ordL (ϖ : w.adicCompletion E) = 1 := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hv : Valued.v (algebraMap E (w.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π).trans hπ
  have h0 : algebraMap E (w.adicCompletion E) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ h0, GlobalTheory.GramParity.ordL_eq_of h0 hv⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RegFn := by
  intro E _ _ _ n w τ B h
  obtain ⟨ϖ, hϖ⟩ := exists_unit_ordL_eq_one w
  obtain ⟨x, hx, htr⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosTr E n w ϖ hϖ τ h.1
  obtain ⟨hL, hS⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosSep E n w ϖ hϖ x hx
  exact ⟨_, hL, htr, hS⟩
