import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_grid_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  first | exact @GlobalTheory.RowReal.ker_rat_left | exact GlobalTheory.RowReal.ker_rat_left | (intros; apply GlobalTheory.RowReal.ker_rat_left <;> assumption)
