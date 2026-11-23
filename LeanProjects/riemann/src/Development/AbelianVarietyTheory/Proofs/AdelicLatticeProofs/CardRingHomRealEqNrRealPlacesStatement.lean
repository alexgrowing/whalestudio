import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardRingHomRealEqNrRealPlaces
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces' : ∀ (F : Type) [Field F] [NumberField F], Nat.card (F →+* ℝ) = InfinitePlace.nrRealPlaces F := by
  first | exact @GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces | exact GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces | (intros; apply GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces <;> assumption)
