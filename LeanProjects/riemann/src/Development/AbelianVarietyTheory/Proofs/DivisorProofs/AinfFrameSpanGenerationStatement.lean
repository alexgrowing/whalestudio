import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSpanGeneration
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frame_span_generation : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N d h : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)) (x : Fin N → Fin h → Ainf p O), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) → h = N * d → Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ x ij.1) = ⊤ → ∃ e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame ρ e ∧ ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
  first | exact @GlobalTheory.DetInv.frame_of_spanning | exact GlobalTheory.DetInv.frame_of_spanning | (intros; apply GlobalTheory.DetInv.frame_of_spanning <;> assumption)
