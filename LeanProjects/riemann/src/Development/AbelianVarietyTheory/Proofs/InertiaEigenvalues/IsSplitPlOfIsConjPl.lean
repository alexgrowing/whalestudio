import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisExportOfMatrixDetBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

open GlobalTheory.TwSys Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ConjugatePlaceSplitting

theorem isSplitPl_of_isConjPl {D : D7} {P P' : PlE D.host} (hs : IsSplitPl D.host P)
    (hc : IsConjPl D.host P P') : IsSplitPl D.host P' := by
  obtain ⟨x, hx, hy⟩ := hs
  have hc' := GlobalTheory.TwistDet.isConjPl_iff.1 hc
  have h1 : GlobalTheory.TwistDet.conjInt D x ∈ P'.asIdeal := (hc' x).1 hx
  have h2 : x ∉ P'.asIdeal := fun h => hy (GlobalTheory.TwistDet.conjInt D x) rfl
    ((hc' (GlobalTheory.TwistDet.conjInt D x)).2 (by rwa [GlobalTheory.TwistDet.conjInt_conjInt]))
  refine ⟨GlobalTheory.TwistDet.conjInt D x, h1, fun y hy' => ?_⟩
  have : y = x := by
    rw [← GlobalTheory.TwistDet.conjInt_conjInt x]
    exact RingOfIntegers.ext hy'
  rwa [this]

end GlobalTheory.ConjugatePlaceSplitting
