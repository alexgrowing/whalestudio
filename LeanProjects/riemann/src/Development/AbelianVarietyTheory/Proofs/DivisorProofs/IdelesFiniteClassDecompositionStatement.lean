import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideles_finite_class_decomposition : ∀ (L : Type) [Field L] [NumberField L],
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ x : (AfE ℚ L)ˣ, ∃ s ∈ S, ∃ a : Lˣ, ∃ k ∈ intU ℚ L, x = s * ratId ℚ L a * k := by
  first | exact @GlobalTheory.ClassCover.exists_finset_cover | exact GlobalTheory.ClassCover.exists_finset_cover | (intros; apply GlobalTheory.ClassCover.exists_finset_cover <;> assumption)
