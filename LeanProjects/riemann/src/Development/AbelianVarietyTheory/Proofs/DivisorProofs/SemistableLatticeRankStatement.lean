import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemistableLatticeRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_lattice_rank : ∀ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = (letters O.S.Dw).length → Full F.lieLat → ∀ (τ : D.host.E →+* ℂ) (k : ℕ), k ≤ O.S.Dw.mult τ → latRank K (stepLat O F τ k) = k := by
  first | exact @GlobalTheory.LieRead.latRank_stepLat | exact GlobalTheory.LieRead.latRank_stepLat | (intros; apply GlobalTheory.LieRead.latRank_stepLat <;> assumption)
