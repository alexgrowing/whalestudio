import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
open GlobalTheory.Sandwich
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne : GlobalTheory.Published.PrismaticDieudonneHodge → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε := by
  first | exact @GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ | exact GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ | (intros; apply GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ <;> assumption)
