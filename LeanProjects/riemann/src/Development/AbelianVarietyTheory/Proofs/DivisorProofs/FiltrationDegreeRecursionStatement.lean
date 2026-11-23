import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationDegreeRecursion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_degree_recursion : ∀ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)), F.P₀.g = (letters O.S.Dw).length → Full F.lieLat → ∀ (τ : D.host.E →+* ℂ) (i : ℕ), i < O.S.Dw.mult τ → deg h (stepLat O F τ (i + 1)) = deg h (stepLat O F τ i) + stepGrDeg O F h τ i := by
  first | exact @GlobalTheory.LieRead.deg_stepLat_succ | exact GlobalTheory.LieRead.deg_stepLat_succ | (intros; apply GlobalTheory.LieRead.deg_stepLat_succ <;> assumption)
