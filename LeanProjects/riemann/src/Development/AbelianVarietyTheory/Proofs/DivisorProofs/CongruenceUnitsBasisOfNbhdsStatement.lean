import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceUnitsBasisOfNbhds
import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_units_basis_of_nbhds : ∀ (L : Type) [Field L] [NumberField L],
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ V : Set (AfE ℚ L)ˣ, IsOpen V → (1 : (AfE ℚ L)ˣ) ∈ V → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ congN ℚ L N, u ∈ V := by
  first | exact @GlobalTheory.CongOpen.exists_congN_subset | exact GlobalTheory.CongOpen.exists_congN_subset | (intros; apply GlobalTheory.CongOpen.exists_congN_subset <;> assumption)
