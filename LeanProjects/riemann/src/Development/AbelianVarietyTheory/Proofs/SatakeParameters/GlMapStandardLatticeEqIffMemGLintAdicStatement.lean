import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 = (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) := by
  first | exact @GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | exact GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | (intros; apply GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint <;> assumption)
