import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpace
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.projectiveBundleFormula_discrete_space : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V :=
  @GlobalTheory.EtC.pbf_disc
