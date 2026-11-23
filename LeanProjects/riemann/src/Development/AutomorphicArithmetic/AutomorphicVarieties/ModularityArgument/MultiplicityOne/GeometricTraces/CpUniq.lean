import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwTrConjEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun

private theorem trc_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (K : Subgroup G) (f : G → ℂ) :
    trc ρ K f = trc ρ' K f := by
  have hid : e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id ∘ₗ e.toLinearEquiv.symm.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact e.toLinearEquiv.apply_symm_apply v
  have h := GlobalTheory.BCT.twTr_conj_equiv G V V' ρ ρ' e K (K ⊓ GlobalTheory.BCT.rStab f ⊓ GlobalTheory.BCT.rStab fun y => f y⁻¹) f LinearMap.id
  rw [hid] at h
  exact h.symm

section Split

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hw]
  trivial

private noncomputable def toUL (hw : IsSplitAt w) (τ : SmIrr (GLw n w)) : SmIrr (UL n w) where
  V := τ.V
  ρ := τ.ρ.comp (UL n w).subtype
  smooth v := (τ.smooth v).preimage continuous_subtype_val
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
    exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, mem_UL hw g⟩ x hx⟩

private theorem isCompU_toUL (hw : IsSplitAt w) {σ : Submodule ℂ (UA E n → ℂ)} {τ : SmIrr (GLw n w)} (h : Cp σ w τ) :
    IsCompU σ w (toUL hw τ) := by
  obtain ⟨-, F, hF0, hFσ, hF⟩ := h
  refine ⟨{ toFun := fun x => ⟨cLoc w x.1, mem_UL hw _⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp) }, fun _ => rfl, (toUL hw τ).irred, F, hF0, hFσ, fun x v => hF x v⟩

private noncomputable def equivOfUL (hw : IsSplitAt w) {τ τ' : SmIrr (GLw n w)} (e : (toUL hw τ).ρ.Equiv (toUL hw τ').ρ) : τ.ρ.Equiv τ'.ρ :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' ⟨g, mem_UL hw g⟩

end Split

theorem UpperTheory.V.Z.Mult.cpUniq :
    UpperTheory.V.Z.Mult.CpUniq := by
  intro E _ _ _ hU n hn σ hσ w hw τ τ' h h'
  obtain ⟨e⟩ := (GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn σ hσ w).2 (toUL hw τ) (toUL hw τ') (isCompU_toUL hw h) (isCompU_toUL hw h')
  have e' := equivOfUL hw e
  exact ⟨fun B hB => GlobalTheory.PrinSat.hasSatGL_of_equiv e'.symm hB, fun f => trc_of_equiv e' _ f⟩
