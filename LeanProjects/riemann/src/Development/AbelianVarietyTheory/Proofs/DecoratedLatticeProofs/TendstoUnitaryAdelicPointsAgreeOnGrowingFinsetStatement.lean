import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset : ∀ (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S), (∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) → Filter.Tendsto x Filter.atTop (nhds κ) := by
  first | exact @GlobalTheory.AdelicLimit.tendsto_of_agree | exact GlobalTheory.AdelicLimit.tendsto_of_agree | (intros; apply GlobalTheory.AdelicLimit.tendsto_of_agree <;> assumption)
