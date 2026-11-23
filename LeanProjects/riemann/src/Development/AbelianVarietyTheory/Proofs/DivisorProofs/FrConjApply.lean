import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport

def adSwap (D : D7) : StandardLatticesGL3.AE D →+* Lev.EAf D :=
  (Lev.swapAE D).comp (GlobalTheory.BotFormula.toAfE D).toRingHom

def inclEAf (D : D7) : D.host.E →+* Lev.EAf D := Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)

def frConj {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) : GL (Fin n) (StandardLatticesGL3.AE D) →* GL (Fin n) (Lev.EAf D) :=
  (MulAut.conj (Formalism.UG.bc (inclEAf D) fr)).toMonoidHom.comp (Formalism.UG.bc (adSwap D))

theorem frConj_apply {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (h : GL (Fin n) (StandardLatticesGL3.AE D)) :
    frConj fr h = Formalism.UG.bc (inclEAf D) fr * Formalism.UG.bc (adSwap D) h * (Formalism.UG.bc (inclEAf D) fr)⁻¹ := rfl

end GlobalTheory.FrameTransport

end
