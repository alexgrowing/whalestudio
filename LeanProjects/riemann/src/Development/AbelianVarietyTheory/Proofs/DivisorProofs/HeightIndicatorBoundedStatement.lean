import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightIndicatorBounded
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_indicator_bounded : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ (τ : D.what₂.Tau) (y : Pt O.s), |H.h0 (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C := by
  first | exact @GlobalTheory.RefFlatHt.refHt | exact GlobalTheory.RefFlatHt.refHt | (intros; apply GlobalTheory.RefFlatHt.refHt <;> assumption)
