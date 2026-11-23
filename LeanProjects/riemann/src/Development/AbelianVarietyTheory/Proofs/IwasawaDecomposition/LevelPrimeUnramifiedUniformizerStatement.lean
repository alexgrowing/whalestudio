import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_unramifiedUniformizer : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT), Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  first | exact @GlobalTheory.LevelUnram.unram | exact GlobalTheory.LevelUnram.unram | (intros; apply GlobalTheory.LevelUnram.unram <;> assumption)
