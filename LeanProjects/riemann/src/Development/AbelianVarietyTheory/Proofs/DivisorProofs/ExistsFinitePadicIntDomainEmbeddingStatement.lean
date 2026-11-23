import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePadicIntDomainEmbedding
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padicInt_domain_embedding : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  first | exact @GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | exact GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | (intros; apply GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain <;> assumption)
