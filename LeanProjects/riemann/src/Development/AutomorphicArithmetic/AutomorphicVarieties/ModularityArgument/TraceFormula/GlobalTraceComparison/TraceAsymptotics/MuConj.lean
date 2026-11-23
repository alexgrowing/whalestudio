import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation

open NumberField IsDedekindDomain Formalism.L2.Host

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.muConj :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.MuConj := by
  intro E _ _ _ μ e hμ w _ hun
  have hc := GlobalTheory.CompanionTheory.MuLocal.loc_mul_loc_conj hμ w
    (Formalism.L2.Host.atFin (GlobalTheory.ThetaSatake.cw w) (Formalism.L2.Host.unif (GlobalTheory.ThetaSatake.cw w)))
  rw [μ.val_eq hun _ (GlobalTheory.CompanionTheory.MuLocal.isUnifAt_conj w _ (Formalism.L2.Host.unif_spec _))] at hc
  exact eq_inv_of_mul_eq_one_left hc
