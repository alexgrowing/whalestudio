import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConePolyLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

set_option maxHeartbeats 400000 in

theorem ConeLocalFlat.proof (h : ConePolyLocalization.Statement.{u}) : ConeLocalFlat.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose v hv using hW.relevant
  obtain ⟨hA, hloc⟩ := h F K ι P hP W hW hPW v hv
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have : IsScalarTower (degZeroLoc P {W}) (MvPolynomial K (degZeroLoc P {W})) (coneLocal P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocal P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl
    exact Module.Flat.trans _ (MvPolynomial K (degZeroLoc P {W})) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
      (coneLocal P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
