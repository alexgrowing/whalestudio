import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → Continuous φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsAutForm.continuous | exact GlobalTheory.CuspRep.IsAutForm.continuous | (intros; apply GlobalTheory.CuspRep.IsAutForm.continuous <;> assumption)
