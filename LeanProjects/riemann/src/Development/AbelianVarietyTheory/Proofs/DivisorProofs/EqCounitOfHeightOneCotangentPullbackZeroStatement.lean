import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D] (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 → ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  first | exact @GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | exact GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | (intros; apply GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero <;> assumption)
