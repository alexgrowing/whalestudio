import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeLatticeElementProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_lattice_element_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ r : RL p O Λ, (∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = 0) → (inA (xi ε) : RL p O Λ) ∣ r := by
  first | exact @GlobalTheory.DetInv.dvd_xi_of_theta_tensor_vanish | exact GlobalTheory.DetInv.dvd_xi_of_theta_tensor_vanish | (intros; apply GlobalTheory.DetInv.dvd_xi_of_theta_tensor_vanish <;> assumption)
