import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_coordinates_bounded_region : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (m n L : ℤ) (κ : GL (Fin 2) F) (R : ℝ) (t : Fˣ), κ ∈ GLnLocal.integralGL F 2 → R ≤ (residueCard F : ℝ) ^ L → (Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ)⁻¹ ∈ Ad3.LFS.om R t → m ≤ L ∧ n ≤ L ∧ (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) ≤ (residueCard F : ℝ) ^ L := by
  first | exact @GlobalTheory.CompanionTheory.LFCoords.coords | exact GlobalTheory.CompanionTheory.LFCoords.coords | (intros; apply GlobalTheory.CompanionTheory.LFCoords.coords <;> assumption)
