import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparison
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_frame_comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ eT eM : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (rhoTA D) eT ∧ IsFrame D.ρM eM ∧ ∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], eT (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j) := by
  first | exact @GlobalTheory.DetInv.frames_exist | exact GlobalTheory.DetInv.frames_exist | (intros; apply GlobalTheory.DetInv.frames_exist <;> assumption)
