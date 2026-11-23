import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.IdemSumAdd

theorem idemSum_union : ∀ (D : D7) (a b : AE D) (P Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), Disjoint P Q → (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → IsIdemSum a P → IsIdemSum b (P ∪ Q) → b = a + ∑ PP ∈ Q, es PP := by
  intro D a b P Q es hPQ hQ ha hb
  rw [← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq hb, GlobalTheory.ExportSeries.idem,
    GlobalTheory.ExportSeries.idem, Finset.sum_union hPQ]
  congr 1
  exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hQ PP hPP)

end GlobalTheory.IdemSumAdd
