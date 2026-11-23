import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_hom_map_ideal_eq : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I := by
  first | exact @GlobalTheory.Prism.Rigid.map_I_eq | exact GlobalTheory.Prism.Rigid.map_I_eq | (intros; apply GlobalTheory.Prism.Rigid.map_I_eq <;> assumption)
