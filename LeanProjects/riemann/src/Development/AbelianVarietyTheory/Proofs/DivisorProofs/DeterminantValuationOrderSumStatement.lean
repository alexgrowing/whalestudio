import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrderSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_valuation_order_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (τ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta τ f → ∀ ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ l₀ : C, v l₀ = v lam ∧ IotaScalar (Φ.F.map ((algebraMap O C).comp f)) (Φ.G.map ((algebraMap O C).comp f)) (D.lieRank τ) l₀ := by
  first | exact @GlobalTheory.DetInv.iotaScalar_of_freeForm | exact GlobalTheory.DetInv.iotaScalar_of_freeForm | (intros; apply GlobalTheory.DetInv.iotaScalar_of_freeForm <;> assumption)
