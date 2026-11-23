import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermLiesOverLocalDatumAfterIsometry
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → ∃ d, Over P d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  first | exact @GlobalTheory.LocOver.GlobOver.over_local | exact GlobalTheory.LocOver.GlobOver.over_local | (intros; apply GlobalTheory.LocOver.GlobOver.over_local <;> assumption)
