import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDoublingJetOfOrderTwoFirstOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRingHomModXPowSuccLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLimitOfDoublingJetsStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem exists_path_ring : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), π.FormallySmooth → ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  intro A B R _ _ _ _ π ε m β δ hsm hεπ hmπ hεm hm2 hδ hδπ
  have step : ∀ n : ℕ, ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) φ →
      ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2 + 1) ψ ∧
        ∀ f, (PowerSeries.X : PowerSeries R) ^ (n + 2) ∣ ψ f - φ f := by
    intro n φ hφ
    obtain ⟨ψ, hψ, hψφ⟩ := GlobalTheory.T.exists_isRingHomModXPow_succ_lift A B R π β hsm (n + 2) (by omega) φ hφ.1
    exact GlobalTheory.T.exists_doublingJet_succ_of_lift A B R π ε m β δ hεπ hmπ hεm hm2 hδ hδπ (n + 2) (by omega) φ ψ hφ hψ hψφ
  choose F hF hFφ using step
  let seq : (n : ℕ) → {φ : A → PowerSeries R // GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) φ} :=
    fun n => Nat.rec ⟨_, GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder A B R π ε m β δ hεπ hmπ hεm hm2 hδ hδπ⟩
      (fun k s => ⟨F k s.1 s.2, hF k s.1 s.2⟩) n
  exact GlobalTheory.T.exists_ringHom_limit_of_doublingJets A B R π ε m β δ (fun n => (seq n).1) (fun n => (seq n).2)
    (fun n f => hFφ n (seq n).1 (seq n).2 f)

end GlobalTheory.Nef
