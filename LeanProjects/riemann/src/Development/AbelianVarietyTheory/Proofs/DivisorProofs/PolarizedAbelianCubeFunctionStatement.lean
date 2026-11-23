import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_cube_function : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)), HasCubeFn A := by
  first | exact @GlobalTheory.WeilIntegral.hasCubeFn | exact GlobalTheory.WeilIntegral.hasCubeFn | (intros; apply GlobalTheory.WeilIntegral.hasCubeFn <;> assumption)
