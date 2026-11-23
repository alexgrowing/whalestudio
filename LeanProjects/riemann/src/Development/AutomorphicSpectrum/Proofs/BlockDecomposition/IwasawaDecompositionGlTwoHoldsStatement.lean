import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_gl_two_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), ∃ (x : F) (m n : ℤ), ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ := by
  first | exact @GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | exact GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | (intros; apply GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two <;> assumption)
