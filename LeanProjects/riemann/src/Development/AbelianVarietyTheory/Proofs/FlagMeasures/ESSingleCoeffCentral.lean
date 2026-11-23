import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabIdem

theorem ES_single_coeff_central : ∀ (D : D7) (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) →
    (∀ γ, (ES {t}).coeff γ = serCoef t γ) ∧ ∀ b, ES {t} * b = b * ES {t} := by
  intro D t _
  have e : (ES {t} : MonoidAlgebra ℂ (G0g D.nd)) = GlobalTheory.RowLev.zTup D t := GlobalTheory.RowLev.ES_singleton (D := D) t
  refine ⟨fun γ => ?_, fun b => ?_⟩
  · rw [e]; rfl
  · rw [e]; exact GlobalTheory.RowLev.zTup_comm t b

end GlobalTheory.LabIdem
