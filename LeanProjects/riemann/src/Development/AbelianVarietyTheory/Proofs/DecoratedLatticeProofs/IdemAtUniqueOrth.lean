import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PlaceIdemUniq

theorem idemAt_unique_orth : ∀ (D : D7) (a b : AE D) (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt a PP → Formalism.L2.NTheta.IsIdemAt b PP' → (PP = PP' → a = b) ∧ (PP ≠ PP' → a * b = 0) := by
  intro D a b PP PP' ha hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split ha) ha hb
  · exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split ha) ha hb h

end GlobalTheory.PlaceIdemUniq
