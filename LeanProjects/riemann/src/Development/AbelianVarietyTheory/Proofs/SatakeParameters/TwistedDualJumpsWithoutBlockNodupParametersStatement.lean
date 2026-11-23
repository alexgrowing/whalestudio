import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsWithoutBlockNodupParameters
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jT2_hcAt_nodup_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (g : D.R.GG) (s : Bool), Roomy L C → (jT2 (hcAt D g) j s).Nodup := by
  first | exact @GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy | exact GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy | (intros; apply GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy <;> assumption)
