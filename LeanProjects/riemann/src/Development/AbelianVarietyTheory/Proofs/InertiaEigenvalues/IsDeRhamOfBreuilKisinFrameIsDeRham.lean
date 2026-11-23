import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isDR_of_frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hF
  obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨B, Q, -, hQ, -, -, hinv⟩ := GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin l K bk τ hτ C N d (fun g => (ρ g).val) F Y hF hY
  have hQ' : IsUnit (T.eD.symm.mapMatrix Q) := hQ.map T.eD.symm.mapMatrix
  refine GlobalTheory.PMon.isDR_of_periodMatrix l P (Fin d) K (Fin d → ℚ_[l]) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hQ'.unit ?_
  intro g
  have hg := hinv g
  simp only [IsUnit.unit_spec]
  ext i j
  apply T.eD.injective
  have hij := congrFun (congrFun hg i) j
  rw [LinearMap.toMatrix_eq_toMatrix']
  simp only [qRep, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.mapMatrix_apply] at hij ⊢
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Units.coeHom_apply, RingHom.mapMatrix_apply, AlgEquiv.coe_toAlgHom, Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_toLin',
    Matrix.map_apply, T.actD, RingEquiv.apply_symm_apply] at ⊢
  rw [← hij]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have e : LinearMap.toMatrix' (Matrix.toLinAlgEquiv' ((algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]))) =
      (algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) :=
    LinearMap.toMatrix'_toLin' _
  erw [e]
  exact T.zD ((ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) i x)

end GlobalTheory.BKLim
