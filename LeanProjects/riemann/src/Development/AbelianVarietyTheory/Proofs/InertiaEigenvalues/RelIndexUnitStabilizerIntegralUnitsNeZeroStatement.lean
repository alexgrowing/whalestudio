import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexUnitStabilizerIntegralUnitsNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero | exact GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero | (intros; apply GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero <;> assumption)
