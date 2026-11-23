import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureOrthonormalFrameEigenOfCartanInvo
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), (∀ i j, star (M j i) = M i j) → M.det ≠ 0 → IsCartan M θ → ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ), IsFrame M A ∧ θ * A = A * Jm r s := by
  first | exact @GlobalTheory.HoweD.FrameCartan.frame_of_cartan | exact GlobalTheory.HoweD.FrameCartan.frame_of_cartan | (intros; apply GlobalTheory.HoweD.FrameCartan.frame_of_cartan <;> assumption)
