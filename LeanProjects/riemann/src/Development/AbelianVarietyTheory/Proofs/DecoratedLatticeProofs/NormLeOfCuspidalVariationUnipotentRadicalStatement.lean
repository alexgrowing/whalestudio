import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ → ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ), (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  first | exact @GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | exact GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | (intros; apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation <;> assumption)
