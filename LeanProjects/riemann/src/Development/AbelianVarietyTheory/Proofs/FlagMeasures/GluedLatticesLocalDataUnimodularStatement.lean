import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodular
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gluedLattices_iff_existsUnique_localDatum : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  first | exact @GlobalTheory.GlueDat.glued_data | exact GlobalTheory.GlueDat.glued_data | (intros; apply GlobalTheory.GlueDat.glued_data <;> assumption)
