import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leviElement_mem_GV {k p ρ : ℕ} (q : Matrix (Fin p) (Fin p) ℂ) (hq : IsUnit q.det) : U.muP k p ρ q ∈ B.GV k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.slice_membership k p ρ).2.1 q (isUnit_iff_ne_zero.mp hq)

def MuPToOm : Prop := ∀ (k p ρ : ℕ) (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ), inWb k (p + ρ) z → inWb k (p + ρ) z' →
  ∀ y ∈ domP k (p + ρ) p z z', y ∈ B.GV k (p + ρ) →
  ∃ q : Matrix (Fin p) (Fin p) ℂ, IsUnit q.det ∧ ∃ V ∈ nhds y, IsCompact V ∧
    ∀ g ∈ V, g ∈ B.GV k (p + ρ) → U.muP k p ρ q * g ∈ JF.Om k (p + ρ) z z'

section zhat

variable {k p ρ : ℕ}

theorem corner_matrix_levi_block_three (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ)
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.muP k p ρ q * U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks ((qᴴ)⁻¹ * (G.wMat p * BlochKatoReduction))
        ((qᴴ)⁻¹ * (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z')))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) := by
  unfold U.muP
  rw [Ux3.block3_mul, Ux3.z_hat_of_block3 z z' hz hz']
  have hw : ∀ M : Matrix (Fin p) (Fin p) ℂ, G.wMat p * (G.wMat p * M * G.wMat p) = M * G.wMat p := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.one_mul]
  congr 2 <;> simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, hw, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc (G.wMat p), hw]; simp only [Matrix.mul_assoc]

theorem zhat_eq_blk (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks (G.wMat p * BlochKatoReduction)
        (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) :=
  Ux3.z_hat_of_block3 z z' hz hz' _ _ _ _ _ _ _ _ _

theorem minor_gen {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hl : m ≤ ρ + 1) (h : p + m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A (Bm.submatrix id (Fin.castLE hl))
        (Cm.submatrix (Fin.castLE hl) id) (Dm.submatrix (Fin.castLE hl) (Fin.castLE hl))) := by
  ext a b
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp [Matrix.reindex_apply, Ux3.eC_symm_castAdd h, Ux3.eC_symm_natAdd h hl]

theorem minor_low {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hmp : m ≤ p) (h : m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE hmp) (Fin.castLE hmp) := by
  have e : ∀ a : Fin m, (Ux3.eC p ρ).symm (Fin.castLE h a) = Sum.inl (Fin.castLE hmp a) := by
    intro a; rw [Equiv.symm_apply_eq]; ext; simp [Ux3.column_index_first_val]
  ext a b
  simp [Matrix.reindex_apply, e]

theorem zh_eq_blk (y : B.Mat k (p + ρ)) :
    G.wMat p * y.submatrix (fun a => U.eB k p ρ (Sum.inr a)) (fun b => U.eB k p ρ (Sum.inl (Sum.inl b))) =
      U.Zh k p ρ y := by
  ext a b
  rw [Ux3.wMat_mul_apply]
  simp only [Matrix.submatrix_apply, U.Zh]
  congr 1
  all_goals (ext; first | (rw [Ux3.block_index_last_val]; simp [Fin.val_rev]; omega) | (rw [Ux3.block_index_first_val]))

theorem minor_leviElement_mul_high (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (m : ℕ) (hm : m ≤ ρ + 1) :
    Dmin k (p + ρ) z z' (U.muP k p ρ q * g) ⟨p + m, by omega⟩ =
      ((qᴴ)⁻¹).det * Dmin k (p + ρ) z z' g ⟨p + m, by omega⟩ := by
  have hg := Ux3.block3_eta g
  unfold Dmin
  rw [hg, corner_matrix_levi_block_three z z' hz hz', zhat_eq_blk z z' hz hz']
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det = _ * ((Matrix.reindex _ _ _).submatrix
      (Fin.castLE (show p + m ≤ p + ρ + 1 by omega)) (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det
  rw [minor_gen _ _ _ _ hm, minor_gen _ _ _ _ hm, Matrix.det_reindex_self, Matrix.det_reindex_self]
  set Q := (qᴴ)⁻¹
  have e : ∀ (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin m) ℂ) (Cm : Matrix (Fin m) (Fin p) ℂ)
      (Dm : Matrix (Fin m) (Fin m) ℂ),
      Matrix.fromBlocks (Q * A) (Q * Bm) Cm Dm = Matrix.fromBlocks Q 0 0 1 * Matrix.fromBlocks A Bm Cm Dm := by
    intro A Bm Cm Dm
    rw [Matrix.fromBlocks_multiply]
    simp
  have hsub : ∀ (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ),
      (Q * Bm).submatrix id (Fin.castLE hm) = Q * Bm.submatrix id (Fin.castLE hm) := by
    intro Bm; ext a b; simp [Matrix.mul_apply]
  rw [hsub, e, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem minor_leviElement_mul_low (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hA : IsUnit (U.Zh k p ρ y).det) (m : ℕ) (hmp : m ≤ p) :
    Dmin k (p + ρ) z z' (U.muP k p ρ (U.Zh k p ρ y)ᴴ * y) ⟨m, by omega⟩ = 1 := by
  have hg := Ux3.block3_eta y
  unfold Dmin
  conv_lhs => rw [hg]
  rw [corner_matrix_levi_block_three z z' hz hz', ← hg]
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show m ≤ p + ρ + 1 by omega))).det = 1
  rw [minor_low _ _ _ _ hmp, zh_eq_blk, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul _ hA]
  have : (1 : Matrix (Fin p) (Fin p) ℂ).submatrix (Fin.castLE hmp) (Fin.castLE hmp) = 1 := by
    ext a b; simp [Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

end zhat

section main

variable {k p ρ : ℕ}

theorem gf_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    Gf k (p + ρ) z z' (U.muP k p ρ q * g) = Complex.normSq ((qᴴ)⁻¹).det * Gf k (p + ρ) z z' g := by
  have e1 : Fin.last (p + ρ + 1) = (⟨p + (ρ + 1), by omega⟩ : Fin (p + ρ + 2)) := Fin.ext rfl
  have e0 : (⟨p + ρ, by omega⟩ : Fin (p + ρ + 2)) = ⟨p + ρ, by omega⟩ := rfl
  unfold Gf
  rw [e1, minor_leviElement_mul_high z z' hz hz' q g (ρ + 1) le_rfl, minor_leviElement_mul_high z z' hz hz' q g ρ (by omega),
    Complex.normSq_mul, Complex.normSq_mul]
  ring

theorem det_Q_ne {A : Matrix (Fin p) (Fin p) ℂ} (hAd : A.det ≠ 0) : (((Aᴴ)ᴴ)⁻¹).det ≠ 0 := by
  rw [Matrix.conjTranspose_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hAd

theorem omPlus_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hy : y ∈ domP k (p + ρ) p z z') (hAd : (U.Zh k p ρ y).det ≠ 0) :
    U.muP k p ρ (U.Zh k p ρ y)ᴴ * y ∈ Q.OmPlus k (p + ρ) z z' := by
  have hQ := det_Q_ne hAd
  refine ⟨fun l hl => ?_, ?_⟩
  · by_cases hlp : l.val ≤ p
    · have e : l = ⟨l.val, by omega⟩ := Fin.ext rfl
      rw [e, minor_leviElement_mul_low z z' hz hz' y (isUnit_iff_ne_zero.mpr hAd) l.val hlp]
      exact one_ne_zero
    · have e : l = ⟨p + (l.val - p), by omega⟩ := Fin.ext (by simp only; omega)
      have hyl := hy.1 l (by omega) hl
      rw [e] at hyl ⊢
      rw [minor_leviElement_mul_high z z' hz hz' _ y (l.val - p) (by omega)]
      exact mul_ne_zero hQ hyl
  · rw [gf_muP z z' hz hz']
    exact mul_pos (Complex.normSq_pos.mpr hQ) hy.2

end main

theorem mem_of_sub_pre {k n : ℕ} {S : Set (B.Mat k n)} {f : B.Mat k n → B.Mat k n} {V : Set (B.Mat k n)}
    (hVO : V ⊆ {g | f g ∈ S}) {g : B.Mat k n} (hg : g ∈ V) : f g ∈ S := hVO hg

theorem mem_Om_of {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {x : B.Mat k r} (h1 : x ∈ B.GV k r)
    (h2 : x ∈ Q.OmPlus k r z z') : x ∈ JF.Om k r z z' := ⟨h1, h2⟩

theorem levi_move_into_big_cell : MuPToOm := by
  intro k p ρ z z' hz hz' y hy hyG
  have hDp : Dmin k (p + ρ) z z' y ⟨p, by omega⟩ ≠ 0 := hy.1 ⟨p, by omega⟩ (le_refl p) (by simp)
  have hAd : (U.Zh k p ρ y).det ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.Ux3.zhDmin k p ρ z z' y
    unfold U.DjU at h
    rw [← h]; exact hDp
  have hqu : IsUnit ((U.Zh k p ρ y)ᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hAd)
  have hy1 := omPlus_muP z z' hz hz' y hy hAd
  have hO : IsOpen {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} :=
    (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus z z').preimage (continuous_const.matrix_mul continuous_id)
  have hy1' : y ∈ {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} := hy1
  have hmem := hO.mem_nhds hy1'
  have hLC : LocallyCompactSpace (B.Mat k (p + ρ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (2 * (p + ρ) + k + 1) → Fin (2 * (p + ρ) + k + 1) → ℂ))
  obtain ⟨V, hV, hVO, hVc⟩ := local_compact_nhds hmem
  refine ⟨(U.Zh k p ρ y)ᴴ, hqu, ?_⟩
  refine ⟨V, hV, hVc, ?_⟩
  intro g hg hgG
  have h1 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ B.GV k (p + ρ) := by
    have hm := leviElement_mem_GV (k := k) (ρ := ρ) (U.Zh k p ρ y)ᴴ hqu
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hm hgG
  have h2 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z' :=
    mem_of_sub_pre (f := fun g => U.muP k p ρ (U.Zh k p ρ y)ᴴ * g) hVO hg
  exact mem_Om_of h1 h2

end Formalism.FourierDecayAlt.P.PBQ
