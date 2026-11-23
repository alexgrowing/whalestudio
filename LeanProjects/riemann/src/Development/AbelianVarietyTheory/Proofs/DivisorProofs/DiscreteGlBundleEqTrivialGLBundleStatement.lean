import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle : ∀ (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), V = trivV N (disc.obj F) := by
  first | (exact @GlobalTheory.EtC.disc_eq_trivV) | (exact GlobalTheory.EtC.disc_eq_trivV) | (intros; apply GlobalTheory.EtC.disc_eq_trivV  <;> assumption)
