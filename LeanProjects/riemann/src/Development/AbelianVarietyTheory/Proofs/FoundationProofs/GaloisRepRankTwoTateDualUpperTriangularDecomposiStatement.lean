import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup <;> assumption)
