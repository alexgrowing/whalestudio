import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLogTeichmullerAssociatedSubOneOnDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_log_teichmuller_associated_sub_one_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  first | exact @GlobalTheory.BSP.SeedT.t_assoc_mu | exact GlobalTheory.BSP.SeedT.t_assoc_mu | (intros; apply GlobalTheory.BSP.SeedT.t_assoc_mu <;> assumption)
