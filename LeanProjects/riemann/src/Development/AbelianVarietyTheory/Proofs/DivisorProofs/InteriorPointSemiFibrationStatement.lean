import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorPointSemiFibration
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interior_point_semi_fibration : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∀ y : Pt O.s, y ∈ H.int → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (ι : K →+* Qb), F.P₀.g = D.R.f * O.N ∧ FibTie O y F ι := by
  first | exact @GlobalTheory.LieRead.fibAt_interior | exact GlobalTheory.LieRead.fibAt_interior | (intros; apply GlobalTheory.LieRead.fibAt_interior <;> assumption)
