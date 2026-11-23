import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMapMaximalIdealOfRingKrullDimEqOne
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by
  first | exact @GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | exact GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | (intros; apply GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one <;> assumption)
