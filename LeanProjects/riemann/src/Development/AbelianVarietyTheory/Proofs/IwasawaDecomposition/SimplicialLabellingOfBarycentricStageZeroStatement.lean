import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab → IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := by
  first | exact @GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | exact GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | (intros; apply GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero <;> assumption)
