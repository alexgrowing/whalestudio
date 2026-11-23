import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ), ((e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q Q'' : Pair k n), Q''.lat = Q.lat → (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧ (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  first | exact @GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd | exact GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd | (intros; apply GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd <;> assumption)
