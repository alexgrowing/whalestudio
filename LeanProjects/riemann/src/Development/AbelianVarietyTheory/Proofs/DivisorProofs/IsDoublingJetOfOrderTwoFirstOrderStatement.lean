import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDoublingJetOfOrderTwoFirstOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM

open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  first | exact @GlobalTheory.Nef.PathJet.firstOrder_isJet | exact GlobalTheory.Nef.PathJet.firstOrder_isJet | (intros; apply GlobalTheory.Nef.PathJet.firstOrder_isJet <;> assumption)
