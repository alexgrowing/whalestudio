import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSecondVariableRapidDecay
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay : ∀ (U V : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (h : SchwartzMap (U × V) ℂ) (k : ℕ), ∃ C : ℝ, ∀ (u : U) (w : V), (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖ ≤ C := by
  first | exact @GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay | exact GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay | (intros; apply GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay <;> assumption)
