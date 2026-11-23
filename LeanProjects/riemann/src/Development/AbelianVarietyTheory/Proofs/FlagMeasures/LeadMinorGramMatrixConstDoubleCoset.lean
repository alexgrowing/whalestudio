import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem leadMinorE_zhatL_dcrel :
    ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E)
      (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T'),
      Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  intro D Λ T T' F F₁ F₂ h l
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := Formalism.L2.SG.Pf.zhat_rel F h
  rw [hZ]
  exact Formalism.L2.SG.Pf.leadMinor_uni A _ B hA0 hA1 hB0 hB1 l

end GlobalTheory
