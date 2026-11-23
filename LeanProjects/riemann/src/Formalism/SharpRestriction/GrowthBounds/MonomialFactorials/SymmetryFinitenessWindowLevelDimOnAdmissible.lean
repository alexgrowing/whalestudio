import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthogonalityWindow
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryFinitenessWindowLevelDimConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestSymm C0 CE1 CE2 X ∧ RestLjjFin C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def SymmetryFinitenessWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryFinitenessWindowLevelDimConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem orthogonal_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : OrthogonalityWindowLevelDimOnAdmissible D :=
  thr_mono_ge (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hCYb hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
    have hp2 : X.p ≠ 2 := by
      intro h2
      have := p25 hF
      have h3 : (X.L.p : ℝ) = 2 := by exact_mod_cast h2
      linarith
    exact ⟨restOrth_of CM hp2 hO a b, c, d⟩) h

theorem closed_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hY : RestYbc) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  integrality_from_metric_of_orthogonality_window D hY (orthogonal_of_symmetric_finite D hO h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
