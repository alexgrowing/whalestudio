import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfTraceOfSmulMemRange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrIsUnit
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range : ∀ (S A B : Type) [CommRing S] [IsLocalRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] [Algebra.Etale S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → (∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) → Function.Surjective φ := by
  first | exact @GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range | exact GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range | (intros; apply GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range <;> assumption)
