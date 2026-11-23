import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryWindowLevelDimOnAdmissible
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LvlDimCondition

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryWindowConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestSymm C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM

def SymmetryWindowOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryWindowConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem windows_of_symmetric_dims (D : Formalism.BasicNotions.D7) (h : SymmetryWindowOnAdmissible D) : SymmetryWindowLevelDimOnAdmissible D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, (lvlDimCondition (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X))⟩) h

theorem closed_of_symmetric_dims (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryWindowOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_windows D hF hO (windows_of_symmetric_dims D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
