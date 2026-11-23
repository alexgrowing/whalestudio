import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerFiltrationIdeal_le_map_of_isDPMorphism : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f → ∀ N, fil δ' N ≤ (fil δ N).map f := by
  first | exact @GlobalTheory.PDA.fil_le_map_fil | exact GlobalTheory.PDA.fil_le_map_fil | (intros; apply GlobalTheory.PDA.fil_le_map_fil <;> assumption)
