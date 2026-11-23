import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM

open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doublingJet_succ_of_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∀ n : ℕ, 2 ≤ n → ∀ φ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ n φ → GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ → (∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f) → ∃ ψ' : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 1) ψ' ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | exact GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | (intros; apply GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift <;> assumption)
