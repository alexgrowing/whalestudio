import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndep
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_element_powers_indep : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | exact GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | (intros; apply GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive <;> assumption)
