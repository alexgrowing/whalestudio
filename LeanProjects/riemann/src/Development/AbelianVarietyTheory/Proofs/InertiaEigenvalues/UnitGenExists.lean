import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem unitGen_exists : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K s LL h) e := by
  intro D HW F l _ K s LL h
  obtain ⟨e, -, -, -, -, hN, -, hφ, hγ, hfree⟩ := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  exact ⟨e, hN, hφ, hγ, hfree⟩

end GlobalTheory.WachUnit
