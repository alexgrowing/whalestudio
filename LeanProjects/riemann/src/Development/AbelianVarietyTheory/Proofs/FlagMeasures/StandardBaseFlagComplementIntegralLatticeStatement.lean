import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardBaseFlag_complement_integralLattice : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → WHyp D (lf D F0) (Wsp D) ∧ Function.Injective (D.sp.iXY 0) ∧ IsPosDef (D.sp.X 0).hT ∧ Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) ∧ Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ (lf D F0)) ∧ detW D (L0X D Λ (lf D F0)) = NT D u ∧ Wb D = Wsp D ⊔ Submodule.span D.host.E {D.zmOf u} := by
  first | exact @GlobalTheory.LoopC.Base.main | exact GlobalTheory.LoopC.Base.main | (intros; apply GlobalTheory.LoopC.Base.main <;> assumption)
