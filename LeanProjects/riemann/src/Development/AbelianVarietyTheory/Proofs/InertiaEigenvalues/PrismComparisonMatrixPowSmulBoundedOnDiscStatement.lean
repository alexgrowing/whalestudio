import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  first | exact @GlobalTheory.BSP.comparisonMatrix_bounded | exact GlobalTheory.BSP.comparisonMatrix_bounded | (intros; apply GlobalTheory.BSP.comparisonMatrix_bounded <;> assumption)
