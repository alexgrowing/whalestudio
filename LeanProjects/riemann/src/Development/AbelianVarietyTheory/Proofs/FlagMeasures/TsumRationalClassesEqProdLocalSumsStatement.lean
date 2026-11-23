import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumRationalClassesEqProdLocalSums
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_rationalClasses_eq_prod_localSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  first | exact @GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | exact GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | (intros; apply GlobalTheory.GenMass.tsum_classes_eq_prod_locSums <;> assumption)
