import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfCoefficientFunction
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestLjjFinProved

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryWindowLevelDimConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestSymm C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def SymmetryWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryWindowLevelDimConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem symmetric_finite_of_windows (D : Formalism.BasicNotions.D7) (h : SymmetryWindowLevelDimOnAdmissible D) : SymmetryFinitenessWindowLevelDimOnAdmissible D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, restLjjFin_proved C0 CE1 CE2 X, b, c⟩) h

theorem closed_of_symmetric_windows (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_coefficient_function D hF hO (symmetric_finite_of_windows D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
