import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied

namespace GlobalTheory.RowClose

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.RowClose.heckeSplitOne_of_charTied : ∀ (D : _root_.Formalism.BasicNotions.D7) (C : _root_.Formalism.L2.Host.CharFrame D)
    (nch : _root_.Formalism.BasicNotions.NChoice D) (Tp : _root_.Formalism.L2.Host.TupTied D C nch), _root_.Formalism.L2.Host.NCharTied D C nch Tp →
    _root_.GlobalTheory.RowCopy.HeckeSplitOne D := by
  intro D C nch Tp T
  have h := _root_.GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut
    (_root_.GlobalTheory.HeckeSplitRow.heckeCharTie_of_tied T)
  unfold _root_.GlobalTheory.ThetaExh.HeckeSplitOne at h
  exact h

end GlobalTheory.RowClose
