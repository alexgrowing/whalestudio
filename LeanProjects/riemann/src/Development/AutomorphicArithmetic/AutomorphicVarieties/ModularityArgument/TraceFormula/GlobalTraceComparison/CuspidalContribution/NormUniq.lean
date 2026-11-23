import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.normUniq :
    NormUniq := by
  intro E _ _ _ N hN π π₀ z hπ h₀ e
  have hI : π.Iso (π₀.twist (Model.absC E z)) := Quotient.exact e.symm
  have hz : z = 0 := PositivityTheory.Rg.Rs.StrStepB.eq_zero_of_iso_twist hN hπ h₀ hI
  subst hz
  have e' := (UpperTheory.ConvolutionTheory.Dp.isoEq E N π (π₀.twist (Model.absC E 0))).1 hI
  rw [PositivityTheory.Rg.Rs.StrStepB.absC_zero, CuspSub.twist_one] at e'
  exact e'.symm
