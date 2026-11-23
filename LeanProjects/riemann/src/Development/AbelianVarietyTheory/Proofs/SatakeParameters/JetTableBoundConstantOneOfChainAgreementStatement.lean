import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.propositionCOneUsedTuples_one_of_tiesAt_sizeAt : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D), (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) → Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  first | exact @GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement | exact GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement | (intros; apply GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement <;> assumption)
