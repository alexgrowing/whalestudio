import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (c : ι → W.EE) (w : ι → RW LL), (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ i, AI.gRW LL (g : GQ l) (w i) = w i) → (∀ i, w i = ∑ j, E.tie.ioE (M i j) * φRW LL (w j) + E.tie.ioE (c i)) → ∀ i, ∃ e : W.EE, E.tie.ioE e = w i := by
  first | exact @GlobalTheory.FrobDescent.mem_range_of_fixed | exact GlobalTheory.FrobDescent.mem_range_of_fixed | (intros; apply GlobalTheory.FrobDescent.mem_range_of_fixed <;> assumption)
