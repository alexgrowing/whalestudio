import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k), (∀ c, τ (algebraMap C O c) = χ c • 1) → finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  first | exact @GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | exact GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_quot_mSub <;> assumption)
