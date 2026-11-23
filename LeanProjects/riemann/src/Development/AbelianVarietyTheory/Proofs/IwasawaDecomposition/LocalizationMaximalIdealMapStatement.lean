import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationMaximalIdealMap
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_maximal_ideal_map : ∀ (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ (IsLocalRing.maximalIdeal B).map (algebraMap B S) → (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → (IsLocalRing.maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  first | exact @GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | exact GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | (intros; apply GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient <;> assumption)
