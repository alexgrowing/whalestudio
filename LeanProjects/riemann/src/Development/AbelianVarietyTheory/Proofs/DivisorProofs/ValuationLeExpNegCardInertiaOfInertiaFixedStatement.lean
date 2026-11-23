import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeExpNegCardInertiaOfInertiaFixed
import Mathlib
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L), (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 → P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by
  first | exact @GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia | exact GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia | (intros; apply GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia <;> assumption)
