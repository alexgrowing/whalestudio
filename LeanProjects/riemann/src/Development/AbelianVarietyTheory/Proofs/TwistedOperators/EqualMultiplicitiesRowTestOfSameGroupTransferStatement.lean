import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransfer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer : ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b) (z : Dat a.st I hX Tw Wt), (GlobalTheory.CuspMult.MultEq (DatCopy.copy b s z).R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧ (Formalism.IndefR.Rat.RowTest ((DatCopy.copy b s z).R.toCx3 (DatCopy.copy b s z).F) → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) := by
  first | exact @GlobalTheory.Twist.multEq_rowTest_of_copy | exact GlobalTheory.Twist.multEq_rowTest_of_copy | (intros; apply GlobalTheory.Twist.multEq_rowTest_of_copy <;> assumption)
