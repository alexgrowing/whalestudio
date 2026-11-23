import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K)) (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  first | exact @GlobalTheory.BSP.fhom_ext_bk | exact GlobalTheory.BSP.fhom_ext_bk | (intros; apply GlobalTheory.BSP.fhom_ext_bk <;> assumption)
