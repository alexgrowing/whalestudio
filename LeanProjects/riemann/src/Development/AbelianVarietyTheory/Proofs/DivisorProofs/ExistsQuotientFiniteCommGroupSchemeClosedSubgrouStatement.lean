import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrou
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A), Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  first | exact @GlobalTheory.HopfQuot.exists_quotient | exact GlobalTheory.HopfQuot.exists_quotient | (intros; apply GlobalTheory.HopfQuot.exists_quotient <;> assumption)
