import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimpleRootCoefEqSuperdiagonalSumFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (N : G.GLV), ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f a.succ) i * G.Hm i j * sig (G.es a j)) = Formalism.L2.SG.PairVal.sgUp B) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) = Formalism.L2.SG.PairVal.sgUp B) := by
  first | exact @GlobalTheory.SlocCoef.main | exact GlobalTheory.SlocCoef.main | (intros; apply GlobalTheory.SlocCoef.main <;> assumption)
