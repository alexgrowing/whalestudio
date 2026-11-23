import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardInertiaEqRamificationIdxOfPerfectResidue
import Mathlib
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)), Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by
  first | exact @GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx | exact GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx | (intros; apply GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx <;> assumption)
