import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.R3.DatCopy

noncomputable section

namespace GlobalTheory.Twist

theorem multEq_rowTest_of_copy : ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b) (z : Dat a.st I hX Tw Wt), (GlobalTheory.CuspMult.MultEq (DatCopy.copy b s z).R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧ (Formalism.IndefR.Rat.RowTest ((DatCopy.copy b s z).R.toCx3 (DatCopy.copy b s z).F) → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) := by
  intro B C a b px I hX Tw Wt s z
  have e := twice_eq b (iK := z.alg) z.R
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := multEq_tr (a := b) a (iK := alg b z.alg) h
    rw [e]
    exact (by with_unfolding_all exact (h2 :))
  · have h2 := rowTest_tr (a := b) a (iK := alg b z.alg) h
    rw [e]
    exact (by with_unfolding_all exact (h2 :))

end GlobalTheory.Twist

end
