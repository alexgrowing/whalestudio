import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_frame_weight_ratio_bound : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c, ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | exact GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio <;> assumption)
