import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedOfHeightOneLocalizations
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.associated_of_height_one_localizations : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (a b : A), a ≠ 0 → b ≠ 0 → (∀ (q : Ideal A) [q.IsPrime], q.height = 1 → Associated (algebraMap A (Localization.AtPrime q) a) (algebraMap A (Localization.AtPrime q) b)) → Associated a b := by
  first | exact @GlobalTheory.associated_of_associated_at_height_one | exact GlobalTheory.associated_of_associated_at_height_one | (intros; apply GlobalTheory.associated_of_associated_at_height_one <;> assumption)
