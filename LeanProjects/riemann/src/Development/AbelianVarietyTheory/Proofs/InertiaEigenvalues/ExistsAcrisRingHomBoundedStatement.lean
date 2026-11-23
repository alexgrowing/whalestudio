import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisRingHomBounded
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_acris_ring_hom_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ γ : Per.Acris l →+* bk.DA bk.ρ₀, (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) ∧ ∀ x, ‖γ x‖ ≤ 1 := by
  first | exact @GlobalTheory.AcrisDisc.exists_acris_to_disc | exact GlobalTheory.AcrisDisc.exists_acris_to_disc | (intros; apply GlobalTheory.AcrisDisc.exists_acris_to_disc <;> assumption)
