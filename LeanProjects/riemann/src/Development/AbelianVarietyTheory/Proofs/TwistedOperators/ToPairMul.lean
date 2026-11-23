import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_mul (p : Pair T) (g k : GA D (G.V p.small)) (h k' : GA D (G.V p.big)) :
    G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
  cases p <;> simp [GridData.toPair, map_mul]

theorem ker_mul (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p f (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') f) g h := by
  simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, Prod.mk.eta, map_mul,
    Module.End.mul_apply]

end GlobalTheory.RowReal
