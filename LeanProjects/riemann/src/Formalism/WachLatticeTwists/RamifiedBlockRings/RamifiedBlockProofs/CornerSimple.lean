import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemFactor

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem blockPoly_corner {K : Type} [Field K] {d S : Type} [Fintype d] [DecidableEq d] [Fintype S]
    [DecidableEq S] (e : Matrix d d K) (U : Matrix d S K) (W : Matrix S d K) (hUW : U * W = e)
    (hWU : W * U = 1) (A : Matrix S S K) : blockPoly e (U * A * W) = A.charpoly := by
  unfold blockPoly Matrix.charpoly Matrix.charmatrix
  let C' : K →+* Polynomial K := Polynomial.C
  have hUW' : U.map C' * W.map C' = e.map C' := by rw [← Matrix.map_mul, hUW]
  have hWU' : W.map C' * U.map C' = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]
  have hx' : (U * A * W).map C' = U.map C' * A.map C' * W.map C' := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
  have h1 : (Polynomial.X : Polynomial K) • e.map C' - (U * A * W).map C' + (1 - e).map C' =
      1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C') := by
    have h2 : (1 - e).map C' = 1 - e.map C' := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [h2, hx', ← hUW']
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, C']

theorem cornerSimple : StatCornerSimple := by
  intro K _ _ d _ _ m c P e hP he hblk
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  obtain ⟨f, hf⟩ : ∃ f, f = P * e * P⁻¹ := ⟨_, rfl⟩
  rw [← hf] at hblk
  have hff : f * f = f := by
    have : P * e * P⁻¹ * (P * e * P⁻¹) = P * (e * (P⁻¹ * P) * e) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [hf, this, hPP', Matrix.mul_one, he]
  have hef : e = P⁻¹ * f * P := by
    have : P⁻¹ * (P * e * P⁻¹) * P = (P⁻¹ * P) * e * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    rw [hf, this, hPP', Matrix.one_mul, Matrix.mul_one]
  let σ : (Σ i, {a // c a = i}) ≃ d := Equiv.sigmaFiberEquiv c
  have hfb : f.submatrix σ σ = Matrix.blockDiagonal' (fun i => f.toSquareBlock c i) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact hblk _ _ (by show c a.1 ≠ c b.1; rw [a.2, b.2]; exact h)
  have hidem : ∀ i, f.toSquareBlock c i * f.toSquareBlock c i = f.toSquareBlock c i := by
    have h1 : Matrix.blockDiagonal' (fun i => f.toSquareBlock c i * f.toSquareBlock c i) =
        Matrix.blockDiagonal' (fun i => f.toSquareBlock c i) := by
      rw [Matrix.blockDiagonal'_mul, ← hfb, Matrix.submatrix_mul_equiv, hff]
    intro i
    exact congrFun (Matrix.blockDiagonal'_injective h1) i
  choose S hS1 hS2 U W hUW hWU using fun i => idem_factor (f.toSquareBlock c i) (hidem i)
  let v : (Σ i, S i) ↪ K :=
    ((Fintype.equivFin (Σ i, S i)).toEmbedding.trans Fin.valEmbedding).trans (Infinite.natEmbedding K)
  let U0 : Matrix d (Σ i, S i) K := (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _)
  let W0 : Matrix (Σ i, S i) d K := (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm
  have hU0W0 : U0 * W0 = f := by
    show (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) *
      (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm = f
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, funext hUW, ← hfb]
    ext a b
    simp
  have hW0U0 : W0 * U0 = 1 := by
    show (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm *
      (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) = 1
    have h1 : (fun i => W i * U i) = 1 := funext hWU
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, h1, Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv _
  have hB : U0 * Matrix.diagonal v * W0 = (Matrix.blockDiagonal' (fun i =>
      U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)).submatrix σ.symm σ.symm := by
    rw [Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_diagonal]
    ext a b
    rfl
  refine ⟨P⁻¹ * (U0 * Matrix.diagonal v * W0) * P, ?_, ?_⟩
  · intro a b hab
    have h1 : P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * P⁻¹ =
        (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [h1, hPP, Matrix.one_mul, Matrix.mul_one, hB]
    show Matrix.blockDiagonal' (fun i => U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)
      ⟨c a, ⟨a, rfl⟩⟩ ⟨c b, ⟨b, rfl⟩⟩ = 0
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  · have h1 : e * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * e =
        (P⁻¹ * U0) * Matrix.diagonal v * (W0 * P) := by
      have h2 : P⁻¹ * f * P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * (P⁻¹ * f * P) =
          P⁻¹ * (f * (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) * f) * P := by
        simp only [Matrix.mul_assoc]
      have h3 : U0 * W0 * (U0 * Matrix.diagonal v * W0) * (U0 * W0) =
          U0 * ((W0 * U0) * Matrix.diagonal v * (W0 * U0)) * W0 := by
        simp only [Matrix.mul_assoc]
      rw [hef, h2, hPP, Matrix.mul_one, Matrix.mul_one, ← hU0W0, h3, hW0U0, Matrix.one_mul,
        Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    have h4 : (P⁻¹ * U0) * (W0 * P) = e := by
      have : (P⁻¹ * U0) * (W0 * P) = P⁻¹ * (U0 * W0) * P := by simp only [Matrix.mul_assoc]
      rw [this, hU0W0, ← hef]
    have h5 : (W0 * P) * (P⁻¹ * U0) = 1 := by
      have : (W0 * P) * (P⁻¹ * U0) = W0 * (P * P⁻¹) * U0 := by simp only [Matrix.mul_assoc]
      rw [this, hPP, Matrix.mul_one, hW0U0]
    rw [h1, blockPoly_corner e _ _ h4 h5, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr v.injective

end Formalism.RepresentationBoundsCohomology.ringDataObjects
