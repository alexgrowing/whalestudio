import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapMaximalIdealEqOfFormallyUnramified
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_maximalIdeal_eq_of_formallyUnramified' : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B], ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  first | exact @GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | exact GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | (intros; apply GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified <;> assumption)
