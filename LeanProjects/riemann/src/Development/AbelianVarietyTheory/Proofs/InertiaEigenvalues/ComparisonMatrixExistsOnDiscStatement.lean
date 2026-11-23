import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonMatrix_exists_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B), ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  first | exact @GlobalTheory.BSP.Height.rel_exists | exact GlobalTheory.BSP.Height.rel_exists | (intros; apply GlobalTheory.BSP.Height.rel_exists <;> assumption)
