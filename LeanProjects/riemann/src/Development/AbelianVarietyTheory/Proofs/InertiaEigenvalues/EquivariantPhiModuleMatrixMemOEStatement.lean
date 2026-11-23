import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_phiModule_matrix_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (X : Matrix (Fin d') (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) → bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) → ∀ i j, X i j ∈ bk.OE := by
  first | exact @GlobalTheory.BSP.EquivOE.main | exact GlobalTheory.BSP.EquivOE.main | (intros; apply GlobalTheory.BSP.EquivOE.main <;> assumption)
