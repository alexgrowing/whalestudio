import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoebImaginaryPartTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moeb_imaginary_part_transform : ∀ {g : ℕ} (γ : Sp g) (T : Matrix (Fin g) (Fin g) ℂ), T.IsSymm → IsUnit (den γ T) → (moeb γ T).map (fun t => (t.im : ℂ)) = ((den γ T)⁻¹)ᴴ * T.map (fun t => (t.im : ℂ)) * (den γ T)⁻¹ := by
  first | exact @GlobalTheory.SiegelMoeb.im_moeb | exact GlobalTheory.SiegelMoeb.im_moeb | (intros; apply GlobalTheory.SiegelMoeb.im_moeb <;> assumption)
