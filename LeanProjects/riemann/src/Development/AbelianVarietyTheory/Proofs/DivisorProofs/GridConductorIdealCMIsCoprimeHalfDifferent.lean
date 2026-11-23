import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem condE_isCoprime_bb {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (h1 : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (h2 : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) : IsCoprime (condE P) D.host.𝔟 :=
  (condE_isCoprime_halfDifferent P ⟨h1, h2⟩).1

end GlobalTheory.FunObj.StdDatum.HalfDiff
