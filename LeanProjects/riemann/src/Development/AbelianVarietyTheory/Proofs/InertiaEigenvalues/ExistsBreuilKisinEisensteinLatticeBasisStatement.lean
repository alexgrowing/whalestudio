import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEisensteinLatticeBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_eisenstein_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m n : ℕ) (Y : Matrix (Fin d) (Fin m) (bk.S)), ∃ (c : ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), X * X' = ((l : bk.S) ^ c * bk.E ^ n) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ X = Y * Q + bk.E ^ n • R ∧ (l : bk.S) ^ c • Y = X * Q' := by
  first | exact @GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis | exact GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis | (intros; apply GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis <;> assumption)
