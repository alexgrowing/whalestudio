import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisedBaseFrames_relevantPair : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → ∀ p : PlF D, (∃ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P) ∧ ∀ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → P.RelG (LocNG.theta (Z.M p)) := by
  first | exact @GlobalTheory.LocBaseRel.atBase_relG | exact GlobalTheory.LocBaseRel.atBase_relG | (intros; apply GlobalTheory.LocBaseRel.atBase_relG <;> assumption)
