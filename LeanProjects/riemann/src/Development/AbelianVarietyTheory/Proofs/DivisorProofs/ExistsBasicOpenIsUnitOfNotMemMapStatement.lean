import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIsUnitOfNotMemMap
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' : ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q → ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀), (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) → ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f, ∀ i, IsUnit (φ (m i)) := by
  first | exact @GlobalTheory.exists_basicOpen_isUnit_of_notMem_map | exact GlobalTheory.exists_basicOpen_isUnit_of_notMem_map | (intros; apply GlobalTheory.exists_basicOpen_isUnit_of_notMem_map <;> assumption)
