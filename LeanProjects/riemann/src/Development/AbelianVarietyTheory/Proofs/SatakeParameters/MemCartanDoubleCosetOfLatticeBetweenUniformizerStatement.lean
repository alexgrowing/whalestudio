import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cartanDoubleCoset_of_lattice_between_uniformizer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)), haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) → ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem | exact GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem | (intros; apply GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem <;> assumption)
