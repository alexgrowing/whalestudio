import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_component_in_range_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ), homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  first | exact @GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem | exact GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem | (intros; apply GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem <;> assumption)
