import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomain
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B → Function.Injective ψ := by
  first | exact @GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | exact GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | (intros; apply GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain <;> assumption)
