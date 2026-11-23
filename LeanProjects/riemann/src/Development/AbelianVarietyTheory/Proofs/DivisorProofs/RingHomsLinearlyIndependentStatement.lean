import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsLinearlyIndependent
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_homs_linearly_independent : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ], Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C), (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  first | exact @GlobalTheory.ringHom_independent_via_algebraMap | exact GlobalTheory.ringHom_independent_via_algebraMap | (intros; apply GlobalTheory.ringHom_independent_via_algebraMap <;> assumption)
