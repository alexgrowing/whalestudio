import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridLastRowColumnCharactersDiffer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGrid_lastRow_column_characters_differ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T),
    ∃ χz : (AE D)ˣ →* Circle, IsHeckeChar D χz ∧ ResEta D χz 1 ∧
      (∀ j, j < D.R.m → G.chrS (.top t j) = G.chrT (.top t j)) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 0 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j) * χz) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 1 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j)) := by
  first | exact @GlobalTheory.RowChars.rowChars | exact GlobalTheory.RowChars.rowChars | (intros; apply GlobalTheory.RowChars.rowChars <;> assumption)
