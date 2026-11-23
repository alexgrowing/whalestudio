import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.MeasInf

def toInfL (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (s : I.Ginf) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J :=
  (Formalism.L2.SG.Measures.splitA I.cm.sig I.J (Formalism.L2.SG.AdBridge.toHA I hb (s, 1))).1

def InfTransfer : Prop :=
  ∀ (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (T : I.F), (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r).IsStd I.cm.sig I.J T →
    ∀ muN muH : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) muN →
      IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH →
      ∃ (μNinf : Measure (Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
          (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r)))
        (μHinf : Measure (Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
          (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r))),
        μNinf.IsHaarMeasure ∧ μHinf.IsHaarMeasure ∧
        Formalism.L2.SG.Measures.amb μNinf = muN.map (toInfL I hb) ∧ Formalism.L2.SG.Measures.amb μHinf = muH.map (toInfL I hb)

end Formalism.L2.SG.Pf.MeasInf
