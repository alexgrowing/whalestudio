import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem haarUniqInf_holds : HaarUniqInf := by
  intro D X u' ψ hT μinf νinf fibInf hP m hinv hfin
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun K hK => hfin K hK⟩
  haveI : m.IsMulLeftInvariant := ⟨fun g => hinv g⟩
  refine ⟨(Measure.haarScalarFactor m X.measG.μGinf : ENNReal), ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul m X.measG.μGinf]
  ext s hs
  simp [Measure.smul_apply]

def WittInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → FbI X u' hT ⊆ Set.range (orbM X u')

theorem regI_of (hW : WittInf) : RegI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  have hc : Continuous (orbM X u') :=
    PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  refine ⟨hc.measurable, fun g => ?_, fun g => (continuous_mul_left g).measurable, fun t =>
    ((continuous_mul_left t).comp continuous_subtype_val).measurable, fun C hC =>
    ⟨hC.isClosed.measurableSet, hC.image hc, (hC.image hc).isClosed.measurableSet⟩,
    hW X u' ψ hT μinf νinf fibInf hP, ?_⟩
  · have hmat : Continuous (fun _ : TupI X =>
        ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := continuous_const
    have : Continuous (fun y : TupI X => g • y) := by
      show Continuous (fun y : TupI X => actTup (Ainf X.B.I.F) (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) y)
      unfold actTup
      exact continuous_pi fun i => hmat.matrix_mulVec ((continuous_apply i))
    exact this.measurable
  · rintro _ ⟨g, rfl⟩
    exact (orbM_mem X u' hT hd g).2

end PI.AprimeInfW
