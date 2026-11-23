import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardGluedMiddleLatticesEqPowPrimeSubOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_gluedMiddleLattices_eq_pow_prime_sub_one : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → IsBase D u F0 → IsRowLat D F0 Λ → ∀ L' ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), (glueSet D u L').Finite ∧ (glueSet D u L').ncard = (Tu D u - 1) ^ D.R.f := by
  first | exact @GlobalTheory.LoopC.GlueCount.main | exact GlobalTheory.LoopC.GlueCount.main | (intros; apply GlobalTheory.LoopC.GlueCount.main <;> assumption)
