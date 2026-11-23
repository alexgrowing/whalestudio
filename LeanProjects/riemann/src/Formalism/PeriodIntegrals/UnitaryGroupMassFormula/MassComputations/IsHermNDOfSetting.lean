import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExFDStabFin

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem isCMExt_of_cmData {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) : IsCMExt F E hc.sig :=
  ⟨hc.totReal, hc.cmUnram.1, hc.deg2, fun τ x => hc.cmUnram.2.1 τ x⟩

theorem isHermND_of_setting {D : D7} (X : HidaSetting D) : IsHermND X.B.I.cm.sig X.B.I.J :=
  ⟨fun i j => congrFun (congrFun X.B.I.J_herm i) j, X.B.I.J_det⟩

theorem discHF_setting {D : D7} (X : HidaSetting D) : DiscreteTopology (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  ((PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds) X.B.I.F X.B.I.E X.B.I.cm.sig
    (isCMExt_of_cmData X.B.I.cm) X.B.I.n X.B.I.J (isHermND_of_setting X)).2

theorem fdExistsH_holds : FDExistsH := by
  intro D X u
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  haveI i1 : SecondCountableTopology (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := inferInstance
  haveI i2 := discHF_setting X
  haveI i3 : SecondCountableTopology (Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let f : ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) →
      HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun x =>
    ⟨((x : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J),
      Subgroup.mem_comap.1 x.2⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) =>
        ((x : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  haveI : DiscreteTopology (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))
    (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
  exact ⟨𝓕, h𝓕 _⟩

end MassDataMassesW
