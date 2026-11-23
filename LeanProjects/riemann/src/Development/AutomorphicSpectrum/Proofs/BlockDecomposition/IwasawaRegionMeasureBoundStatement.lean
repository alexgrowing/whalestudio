import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_region_measure_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (m n L : ℤ), IsOpen {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ∧ (n ≤ L → μ {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ≤ ENNReal.ofReal ((residueCard F : ℝ) ^ (L - n)) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume | exact GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume | (intros; apply GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume <;> assumption)
