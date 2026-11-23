import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLocalCongruence

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

theorem compK_holds : CompK := by
  intro D X v h hh
  exact (Subgroup.mem_iInf.1 hh) v

theorem compH_holds : CompH := by
  intro D X w v h hh
  unfold Hsub at hh ⊢
  rw [mem_stabT] at hh ⊢
  intro b
  funext i
  have hi := congrFun (hh b) i
  change (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j *
      inclR (Af X.B.I.F) (tupH (frameOf X w) b j)) = inclR (Af X.B.I.F) (tupH (frameOf X w) b i) at hi
  change (∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j *
      inclR (Fv X.B.I.F v) (tupH (frameOf X w) b j)) = inclR (Fv X.B.I.F v) (tupH (frameOf X w) b i)
  rw [← tensMap_inclR (E := X.B.I.E) (evalV X.B.I.F v) (tupH (frameOf X w) b i), ← hi, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

section Fin

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finHA_mul (x y : X.B.I.Gf) : finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), x * y) = (1, x) * (1, y) by simp, map_mul, map_mul, Prod.snd_mul]

theorem finHA_one : finHA X hb 1 = 1 := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), (1 : X.B.I.Gf)) = 1 from rfl, map_one, map_one, Prod.snd_one]

theorem finHA_inv (x : X.B.I.Gf) : finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), x⁻¹) = (1, x)⁻¹ by simp, map_inv, map_inv, Prod.snd_inv]

end Fin

theorem k2uGrp_holds : ConjugateLevelIsSubgroup := by
  intro D X hb hK w
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨finHA X hb 1, ⟨1, hK.1, rfl⟩, ?_⟩
    simp only [finHA_one, mul_one, mul_inv_cancel]
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb', rfl⟩, rfl⟩
    refine ⟨finHA X hb (a * b), ⟨a * b, hK.2.1 a ha b hb', rfl⟩, ?_⟩
    simp only [finHA_mul]
    group
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨finHA X hb a⁻¹, ⟨a⁻¹, hK.2.2.1 a ha, rfl⟩, ?_⟩
    simp only [finHA_inv]
    group

end MassDataLevelSSteps
