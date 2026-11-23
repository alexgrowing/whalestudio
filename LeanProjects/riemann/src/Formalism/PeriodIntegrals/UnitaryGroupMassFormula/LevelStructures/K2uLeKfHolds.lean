import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finHA_mem_Kf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf)
    (hx : x ∈ X.B.I.Kset) :
    finHA X hb x ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb x).2 hx

theorem k2uLeKf_holds : ConjugateLevelLeMaximalCompact := by
  intro D X hb _ hL w
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have h1 := finHA_mem_Kf X hb (X.xu w) (X.xu_K w)
  have h2 := finHA_mem_Kf X hb k (hL.2.1 k hk)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)

end MassDataLevelSSteps
