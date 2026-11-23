import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumberFieldGLDenseInCompletionGLTwoSided
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first | exact @GlobalTheory.DenseGL.dense_two_sided | exact GlobalTheory.DenseGL.dense_two_sided | (intros; apply GlobalTheory.DenseGL.dense_two_sided <;> assumption)
