import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.MinInf

theorem opNorm_le_one_of_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    opNorm U ≤ 1 := by
  have h1 : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  set T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U with hT
  have h2 : star T * T = 1 := by
    rw [hT, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h1, map_one]
  have h3 : ‖T‖ * ‖T‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, h2]
    exact ContinuousLinearMap.norm_id_le
  have h4 : ‖T‖ ≤ 1 := by
    by_contra h
    have h' : 1 < ‖T‖ := not_le.1 h
    nlinarith
  exact_mod_cast h4

theorem nnnorm_entry_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ ι) d = A i j
    simp
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnnorm_apply_le _ i).trans h2

theorem nnnorm_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ≥0) (h : ∀ i j, ‖M i j‖₊ ≤ c) :
    ‖M.det‖₊ ≤ (n.factorial : ℝ≥0) * c ^ n := by
  have h1 := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := (c : ℝ))
    (fun i j => NNReal.coe_le_coe.2 (h i j))
  simp only [Fintype.card_fin, nsmul_eq_mul] at h1
  exact_mod_cast h1

theorem minor_le {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A κ : Matrix ι ι R) (c : ℝ≥0) (hA : opNorm (A.map φ) ≤ c) (hκ : κ.map φ * (κ.map φ)ᴴ = 1) (f e : Fin n → ι) :
    ‖φ ((A * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * c ^ n := by
  have hAU : opNorm (A.map φ * κ.map φ) ≤ c :=
    (opNorm_mul_le _ _).trans ((mul_le_of_le_one_right' (opNorm_le_one_of_unitary _ hκ)).trans hA)
  have hdet : φ ((A * κ).submatrix f e).det = ((A.map φ * κ.map φ).submatrix f e).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul]
  rw [hdet]
  exact nnnorm_det_le _ c fun i j => (nnnorm_entry_le (A.map φ * κ.map φ) (f i) (e j)).trans hAU

theorem opNorm_le_htInf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (AE F E)) :
    opNorm (X.1.map (piInf τ)) ≤ htInf F w (Formalism.UG.bc (compInf F E w) X) := by
  have e : X.1.map (piInf τ) = ((Formalism.UG.bc (compInf F E w) X).1).map (infEmb τ) := by
    ext i j
    rfl
  rw [e]
  exact ((normInf_le_iff F w).1 le_rfl τ).trans (le_htOf (normInf F w) (Formalism.UG.bc (compInf F E w) X))

theorem minor_le_htInf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (AE F E))
    (κ : Matrix ι ι (AE F E)) (hκ : κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1) (f e : Fin n → ι) :
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤
      (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n :=
  minor_le (piInf τ) X.1 κ _ (opNorm_le_htInf F E ι w τ X) hκ f e

end GlobalTheory.CompanionTheory.GodementH.MinInf
end
