import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimePeriodRow_of_constructedPointChains : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) → Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i, Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  first | exact @GlobalTheory.AtG.row_atG_of_jetSplitAmb | exact GlobalTheory.AtG.row_atG_of_jetSplitAmb | (intros; apply GlobalTheory.AtG.row_atG_of_jetSplitAmb <;> assumption)
