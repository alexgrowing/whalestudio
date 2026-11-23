import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

theorem embedding_map_embedded_group : MMapEmbG := by
  intro k p ρ Z γ y₁ y₂
  simp only [U.mMap, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem embedded_group_measure_preserving : EmbGMuP := by
  intro k p ρ y q
  simp only [U.muP, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem wMat_mul_self_eq_one (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  split_ifs <;> simp_all

private theorem wMat_mul_wMat_mul' (d : ℕ) {m : Type*} (X : Matrix (Fin d) m ℂ) : G.wMat d * (G.wMat d * X) = X := by
  rw [← Matrix.mul_assoc, wMat_mul_self_eq_one, Matrix.one_mul]

theorem embedding_map_lower_unipotent : MMapLZU := by
  intro k p ρ l Z u γ hl
  simp only [U.mMap, U.muP, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_nonsing_inv l hl,
    Matrix.mul_assoc, wMat_mul_wMat_mul']

theorem embedded_group_right_action : EmbGRn := by
  intro k p ρ y x hy
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have h2 : (rcAct y x).2 = x.2 := rfl
  have h3 : yᴴ * (Hpk k ρ * y) = Hpk k ρ := by rw [← Matrix.mul_assoc, hy]
  have h4 : ∀ M : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ, yᴴ * (Hpk k ρ * (y * M)) = Hpk k ρ * M := by
    intro M
    rw [← Matrix.mul_assoc (Hpk k ρ), ← Matrix.mul_assoc, h3]
  simp only [U.Rn, U.embG, Ux5.block3_mul_blocks, h1, h2, Matrix.conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3, h4,
    neg_zero, smul_zero]

private theorem wP_inv_mul_wP_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ⁻¹ * U.wP σ = 1 := by
  ext a c
  have h : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
  simp only [U.wP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h]

private theorem isUnit_det_wP {p : ℕ} (σ : Equiv.Perm (Fin p)) : IsUnit (U.wP σ).det :=
  Matrix.isUnit_det_of_left_inverse (wP_inv_mul_wP_eq_one σ)

theorem lh_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : G.IsLowerUni (lhOf σ v) := by
  have hinv : (U.wP σ)⁻¹ = U.wP σ⁻¹ := Matrix.inv_eq_left_inv (wP_inv_mul_wP_eq_one σ)
  have hentry : ∀ a b, lhOf σ v a b = U.lowW σ v (σ a) (σ b) := by
    intro a b
    rw [lhOf, hinv]
    simp only [Matrix.mul_apply, U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.Perm.inv_eq_iff_eq, Finset.sum_ite_eq']
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Matrix.transpose_apply, hentry]
    simp [U.lowW]
  · simp only [Matrix.transpose_apply, hentry]
    have h1 : σ j ≠ σ i := fun h => (ne_of_lt hij) (σ.injective h)
    have h2 : ¬ (i < j) := not_lt.mpr hij.le
    simp [U.lowW, Matrix.one_apply, h1, h2]

theorem head_hermitian_eq : HeadHEq := by
  intro p σ d v u
  refine ⟨?_, lh_lower σ v⟩
  simp only [U.headH, lhOf, U.hMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), Matrix.nonsing_inv_mul _ (isUnit_det_wP σ), Matrix.one_mul]

private theorem blk2_fin_zero_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 0) ℂ)
    (C : Matrix (Fin 0) (Fin p) ℂ) (D : Matrix (Fin 0) (Fin 0) ℂ) : U.blk2 A B' C D = A := by
  ext i j
  have hi : finSumFinEquiv.symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  have hj : finSumFinEquiv.symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  simp [U.blk2, Matrix.reindex_apply, hi, hj]

theorem lower_corner_hermitian_zero : ZjHZero := by
  intro p σ d η Z
  simp only [U.ZjH, U.Zj, blk2_fin_zero_eq, Matrix.one_mul, Matrix.mul_one]

theorem lh_unit {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : IsUnit (lhOf σ v).det := by
  have hL : (U.lowW σ v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ?_]
    · simp [U.lowW]
    · intro i j hij
      have h1 : i < j := OrderDual.toDual_lt_toDual.mp hij
      have h2 : ¬ j < i := not_lt.mpr h1.le
      simp [U.lowW, Matrix.one_apply, ne_of_lt h1, h2]
  simp only [lhOf, Matrix.det_mul, hL, mul_one]
  exact (isUnit_det_wP σ).mul (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_wP σ))

theorem gamma_xi_split : GaXiSplit := by
  intro k p ρ σ d ξ Z h ν h' ν' g hh hν hh'
  have hZ : U.ZjH σ d ξ.2 Z = lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2 := by
    rw [lower_corner_hermitian_zero p σ d ξ.2 Z]
    exact (head_hermitian_eq p σ d ξ.2.2.1 ξ.2.2.2).1
  have hγ : h⁻¹ * ν⁻¹ * g * ν' * h' = (h⁻¹ * ν⁻¹) * g * (ν' * h') := by
    simp only [Matrix.mul_assoc]
  have hE : U.embG k p ρ (ν' * h') = U.embG k p ρ ν' * U.embG k p ρ h' := by
    simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  simp only [U.gaXi]
  rw [PBM.rn_inv, hZ]
  show U.Rn k p ρ (-ξ.1.1) * U.mMap k p ρ (lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2) (h⁻¹ * ν⁻¹ * g * ν' * h') *
      U.Rn k p ρ ξ.1.2 = _
  rw [embedding_map_lower_unipotent k p ρ _ _ _ _ (lh_unit σ ξ.2.2.1), hγ, embedding_map_embedded_group, hE]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.embG k p ρ h') (U.muP k p ρ (G.upper ξ.2.2.2)),
    embedded_group_measure_preserving k p ρ h' (G.upper ξ.2.2.2), Matrix.mul_assoc, embedded_group_right_action k p ρ h' ξ.1.2 hh']

theorem embG_nset {k p ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ QuantumDeterminants.Nset k ρ) : U.embG k p ρ y ∈ QuantumDeterminants.Nset k (p + ρ) := by
  rw [WeylGroupFacts.nset_iff] at hy ⊢
  refine ⟨?_, ?_⟩
  · show (U.embG k p ρ y)ᴴ * Hpk k (p + ρ) * U.embG k p ρ y = Hpk k (p + ρ)
    have hy1 : yᴴ * Hpk k ρ * y = Hpk k ρ := hy.1
    rw [Formalism.FourierDecayAlt.P.hermitian_group_blocks k p ρ, U.embG, Ux3.block3_conjTranspose, Ux3.block3_mul, Ux3.block3_mul]
    congr 1 <;> simp [hy1]
  · intro i c hc hi
    obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
    obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective c
    rw [U.embG, Ux3.block3_apply]
    simp only [(U.eB k p ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases w with ((w | w) | w) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc hi <;>
      first
      | (simp [Matrix.one_apply]; done)
      | (exfalso; have := x.isLt; have := w.isLt; omega)
      | skip
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]
    exact hy.2 x w (by omega) (by omega)

theorem left_factor_mem : LeftMem := by
  intro k p ρ z x l h ν hz hl hh hν
  have hH := Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ
  have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have hclN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)

  have hlH : G.IsUpperUni lᴴ := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_apply, show l i i = lᵀ i i from rfl, hl.1 i, star_one]
    · rw [Matrix.conjTranspose_apply, show l j i = lᵀ i j from rfl, hl.2 i j hij, star_zero]
  have hlu : IsUnit (lᴴ).det := by rw [Formalism.FourierDecayAlt.P.G4.upperUni_det hlH]; exact isUnit_one
  have hmu : U.muP k p ρ (lᴴ)⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) := by
    rw [← Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hlu]
    refine hclN.inv_mem _ (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ ⟨fun i j hij => hlH.2 i j hij, hlH.1⟩)
  have hRn : U.Rn k p ρ (rcAct h x) ∈ QuantumDeterminants.Nset k (p + ρ) :=
    (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨rcAct h x, rfl⟩)
  have hνN : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) :=
    embG_nset ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).inv_mem ν hν)
  have hW : U.embG k p ρ h⁻¹ ∈ UWset k (p + ρ) (liftVec k p ρ z) := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]; exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW p ρ z _ (WeylGroupFacts.uw_inv hh)
  refine ⟨U.embG k p ρ h⁻¹, hW, U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ ν⁻¹,
    hclN.mul_mem _ (hclN.mul_mem _ hRn _ hmu) _ hνN, ?_⟩
  have e1 : U.embG k p ρ h * U.Rn k p ρ x = U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := embedded_group_right_action k p ρ h x hh.1
  have e2 : U.embG k p ρ h⁻¹ * U.embG k p ρ h = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, Matrix.nonsing_inv_mul _ hhu, Formalism.FourierDecayAlt.P.PBM.embG_one]
  have e3 : U.Rn k p ρ x = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  have e4 : U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹) = U.embG k p ρ ν⁻¹ := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  have e5 : U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹ = U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ h := embedded_group_measure_preserving k p ρ h _
  calc U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)
      = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * (U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹) *
          U.embG k p ρ (h⁻¹ * ν⁻¹) := by rw [e3]; simp only [Matrix.mul_assoc]
    _ = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ *
          (U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹)) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e4]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
