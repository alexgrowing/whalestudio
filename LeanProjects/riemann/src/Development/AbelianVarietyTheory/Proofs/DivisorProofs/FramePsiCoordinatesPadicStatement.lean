import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePsiCoordinatesPadic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_psi_coordinates_padic : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → (∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j)) → ∀ w, e (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  first | exact @GlobalTheory.DetInv.frame_psi_eq_phiInv | exact GlobalTheory.DetInv.frame_psi_eq_phiInv | (intros; apply GlobalTheory.DetInv.frame_psi_eq_phiInv <;> assumption)
