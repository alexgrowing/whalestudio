import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FullRankPair

variable {k : Type} [Field k]

theorem exists_right_inv {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) (hM : M.rank = n) :
    ∃ T : Matrix (Fin d) (Fin n) k, M * T = 1 := by
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hM]; simp
  have hs : Function.Surjective M.mulVecLin := LinearMap.range_eq_top.mp hrange
  refine ⟨Matrix.of fun j i => Function.surjInv hs (Pi.single i 1) j, ?_⟩
  ext a i
  have := congrFun (Function.surjInv_eq hs (Pi.single i 1)) a
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [this]; simp [Pi.single_apply, eq_comm]

theorem exists_bound {ι : Type} [Fintype ι] (f : ι → k) [ValuativeRel k] :
    ∃ c : k, c ≠ 0 ∧ ∀ i, ValuativeRel.valuation k (c * f i) ≤ 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_ne_zero, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => ValuativeRel.valuation k (f i)) Finset.univ_nonempty
  by_cases h0 : f i₁ = 0
  · refine ⟨1, one_ne_zero, fun i => ?_⟩
    have := hi₁ i (Finset.mem_univ _)
    simp only [h0, map_zero] at this
    simp [le_antisymm this zero_le']
  · refine ⟨(f i₁)⁻¹, inv_ne_zero h0, fun i => ?_⟩
    have := hi₁ i (Finset.mem_univ _)
    rw [map_mul, map_inv₀]
    have hv : ValuativeRel.valuation k (f i₁) ≠ 0 := by simpa using h0
    exact inv_mul_le_one_of_le₀ this zero_le'

theorem exists_ker {n d : ℕ} (Y₁ Y₂ : Matrix (Fin n) (Fin d) k) (h₁ : Y₁.rank = n)
    (h₂ : Y₂.rank = n) (hne : ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) :
    ∃ u : Fin d → k, Y₂ *ᵥ u = 0 ∧ Y₁ *ᵥ u ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨T₀, hT₀⟩ := exists_right_inv Y₂ h₂
  obtain ⟨T₁, hT₁⟩ := exists_right_inv Y₁ h₁
  have hfac : Y₁ * T₀ * Y₂ = Y₁ := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply]
    have hv : Y₂ *ᵥ (v - T₀ *ᵥ (Y₂ *ᵥ v)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hT₀, Matrix.one_mulVec, sub_self]
    have := H _ hv
    rw [Matrix.mulVec_sub, sub_eq_zero] at this
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hab : (Y₁ * T₀) * (Y₂ * T₁) = 1 := by
    rw [← Matrix.mul_assoc, hfac, hT₁]
  exact hne ⟨Y₁ * T₀, Y₂ * T₁, hab, mul_eq_one_comm.mp hab⟩ hfac.symm

def pivotMat {m : ℕ} (x ψ : Fin m → k) (i : Fin m) : Matrix (Fin m) (Fin m) k :=
  1 - (x i)⁻¹ • Matrix.vecMulVec x (Pi.single i 1) + Matrix.vecMulVec (Pi.single i 1) ψ

theorem pivotMat_row {m : ℕ} (x ψ : Fin m → k) (i : Fin m) (hx : x i ≠ 0) (j : Fin m) :
    pivotMat x ψ i i j = ψ j := by
  by_cases hij : j = i
  · subst hij; simp [pivotMat, Matrix.vecMulVec_apply, hx]
  · simp [pivotMat, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply, hij, Ne.symm hij]

theorem pivotMat_mulVec {m : ℕ} (x ψ : Fin m → k) (i : Fin m) (hx : x i ≠ 0) (h1 : ψ ⬝ᵥ x = 1) :
    pivotMat x ψ i *ᵥ x = Pi.single i 1 := by
  simp only [pivotMat, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.one_mulVec, single_dotProduct, h1, one_mul, op_smul_eq_smul, one_smul, smul_smul,
    inv_mul_cancel₀ hx, sub_self, zero_add]

theorem pivotMat_isUnit {m : ℕ} (x ψ : Fin m → k) (i : Fin m) (hx : x i ≠ 0) (h1 : ψ ⬝ᵥ x = 1) :
    IsUnit (pivotMat x ψ i) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  simp only [pivotMat, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.one_mulVec, single_dotProduct, one_mul, op_smul_eq_smul, smul_smul] at hy
  have hi := congrFun hy i
  have hc : (x i)⁻¹ * y i * x i = y i := by field_simp
  simp [hc] at hi
  rw [hi, zero_smul, add_zero, sub_eq_zero] at hy
  have hψ : ψ ⬝ᵥ y = (x i)⁻¹ * y i := by
    conv_lhs => rw [hy]
    rw [dotProduct_smul, h1, smul_eq_mul, mul_one]
  rw [hi] at hψ
  have hyi : y i = 0 := by
    rcases mul_eq_zero.mp hψ.symm with h | h
    · exact absurd h (inv_ne_zero hx)
    · exact h
  apply hy0
  rw [hy, hyi, mul_zero, zero_smul]

theorem row_mul {l m o : ℕ} (A : Matrix (Fin l) (Fin m) k) (B : Matrix (Fin m) (Fin o) k) (i : Fin l) :
    (A * B) i = A i ᵥ* B := rfl

theorem unit_of_diag {m : ℕ} (i : Fin m) (μ : k) (hμ : μ ≠ 0) :
    IsUnit (Matrix.diagonal (fun a : Fin m => if a = i then (1 : k) else μ)) := by
  rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro a
  split_ifs
  · exact isUnit_one
  · exact isUnit_iff_ne_zero.mpr hμ

end GlobalTheory.FullRankPair

open GlobalTheory.FullRankPair in

theorem GlobalTheory.FullRankPair.pair_normal_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Y₁.rank = n → Y₂.rank = n →
    (∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
    ∃ (i₀ : Fin n) (j₀ : Fin d) (g : GL (Fin n) k) (h : GL (Fin d) k),
      (∀ i j, ValuativeRel.valuation k (((g.1)ᵀ * Y₁ * h.1) i j) ≤ 1) ∧
      (∀ j, ((g.1)ᵀ * Y₁ * h.1) i₀ j = if j = j₀ then 1 else 0) ∧
      (∀ i, i ≠ i₀ → ((g.1)ᵀ * Y₁ * h.1) i j₀ = 0) ∧ (∀ i, (Y₂ * h.1) i j₀ = 0) ∧
      ∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, ValuativeRel.valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧
        Y₂ * h.1 * S = 1 := by
  intro k _ _ _ _ n d Y₁ Y₂ h₁ h₂ hne
  obtain ⟨u, hu2, hu1⟩ := exists_ker Y₁ Y₂ h₁ h₂ hne
  obtain ⟨i₀, hz⟩ : ∃ i, (Y₁ *ᵥ u) i ≠ 0 := by
    by_contra H; push_neg at H; exact hu1 (funext H)
  obtain ⟨j₀, hu⟩ : ∃ j, u j ≠ 0 := by
    by_contra H; push_neg at H
    apply hu1; rw [show u = 0 from funext H, Matrix.mulVec_zero]

  obtain ⟨w, hw⟩ : ∃ w : Fin n → k, w = ((Y₁ *ᵥ u) i₀)⁻¹ • Pi.single i₀ 1 := ⟨_, rfl⟩
  have hwz : w ⬝ᵥ (Y₁ *ᵥ u) = 1 := by
    rw [hw, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, inv_mul_cancel₀ hz]
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin d → k, φ = w ᵥ* Y₁ := ⟨_, rfl⟩
  have hφu : φ ⬝ᵥ u = 1 := by rw [hφ, ← Matrix.dotProduct_mulVec]; exact hwz

  obtain ⟨T₀, hT₀⟩ := exists_right_inv Y₂ h₂
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin d) (Fin n) k, T = T₀ - Matrix.vecMulVec u (φ ᵥ* T₀) := ⟨_, rfl⟩
  have hT : Y₂ * T = 1 := by
    rw [hTdef, Matrix.mul_sub, Matrix.mul_vecMulVec, hu2, hT₀]
    ext a b; simp [Matrix.vecMulVec_apply]
  have hφT : φ ᵥ* T = 0 := by
    rw [hTdef, Matrix.vecMul_sub, Matrix.vecMul_vecMulVec, hφu, one_smul, sub_self]

  have hPd := pivotMat_isUnit u φ j₀ hu hφu
  obtain ⟨μ, hμ0, hμ⟩ := exists_bound (fun p : Fin d × Fin n => (pivotMat u φ j₀ * T) p.1 p.2)
  obtain ⟨Qd, hQd⟩ : ∃ Q : Matrix (Fin d) (Fin d) k,
      Q = Matrix.diagonal (fun a => if a = j₀ then (1 : k) else μ) * pivotMat u φ j₀ := ⟨_, rfl⟩
  have hQdu : IsUnit Qd := hQd ▸ (unit_of_diag j₀ μ hμ0).mul hPd
  have hQrow : Qd j₀ = φ := by
    ext b; rw [hQd, Matrix.diagonal_mul, if_pos rfl, one_mul, pivotMat_row u φ j₀ hu]
  have hQu : Qd *ᵥ u = Pi.single j₀ 1 := by
    rw [hQd, ← Matrix.mulVec_mulVec, pivotMat_mulVec u φ j₀ hu hφu, Matrix.diagonal_mulVec_single,
      if_pos rfl, one_mul]
  let h : GL (Fin d) k := hQdu.unit⁻¹
  have hhQ : h.1 * Qd = 1 := hQdu.val_inv_mul
  have hQh : Qd * h.1 = 1 := hQdu.mul_val_inv
  have hhe : h.1 *ᵥ Pi.single j₀ 1 = u := by
    rw [← hQu, Matrix.mulVec_mulVec, hhQ, Matrix.one_mulVec]
  have hφh : φ ᵥ* h.1 = Pi.single j₀ 1 := by
    rw [← hQrow, ← row_mul, hQh]; ext b; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

  have hPn := pivotMat_isUnit (Y₁ *ᵥ u) w i₀ hz hwz
  obtain ⟨ν, hν0, hν⟩ := exists_bound (fun p : Fin n × Fin d => (pivotMat (Y₁ *ᵥ u) w i₀ * Y₁ * h.1) p.1 p.2)
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) k,
      G = Matrix.diagonal (fun a => if a = i₀ then (1 : k) else ν) * pivotMat (Y₁ *ᵥ u) w i₀ := ⟨_, rfl⟩
  have hGu : IsUnit G := hG ▸ (unit_of_diag i₀ ν hν0).mul hPn
  have hGtu : IsUnit Gᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]; exact hGu
  have hGrow : G i₀ = w := by
    ext b; rw [hG, Matrix.diagonal_mul, if_pos rfl, one_mul, pivotMat_row _ w i₀ hz]
  have hGz : G *ᵥ (Y₁ *ᵥ u) = Pi.single i₀ 1 := by
    rw [hG, ← Matrix.mulVec_mulVec, pivotMat_mulVec _ w i₀ hz hwz, Matrix.diagonal_mulVec_single,
      if_pos rfl, one_mul]
  let g : GL (Fin n) k := hGtu.unit
  have hgG : (g.1)ᵀ = G := by simp [g]
  have hrow : ∀ j, ((g.1)ᵀ * Y₁ * h.1) i₀ j = if j = j₀ then 1 else 0 := by
    intro j
    rw [hgG, row_mul, row_mul, hGrow, ← hφ, hφh, Pi.single_apply]
  refine ⟨i₀, j₀, g, h, ?_, hrow, ?_, ?_, ?_⟩
  · intro i j
    by_cases hi : i = i₀
    · subst hi; rw [hrow j]; split_ifs <;> simp
    · have := hν (i, j)
      rw [hgG, hG, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul, if_neg hi,
        ← Matrix.mul_assoc]
      exact this
  · intro i hi
    have : ((g.1)ᵀ * Y₁ * h.1) *ᵥ Pi.single j₀ 1 = Pi.single i₀ 1 := by
      rw [← Matrix.mulVec_mulVec, hhe, ← Matrix.mulVec_mulVec, hgG, hGz]
    have := congrFun this i
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply, hi] using this
  · intro i
    have := congrFun (show (Y₂ * h.1) *ᵥ Pi.single j₀ 1 = 0 by rw [← Matrix.mulVec_mulVec, hhe, hu2]) i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  · have hSrow : ∀ i, (Qd * T) j₀ i = 0 := by
      intro i; rw [row_mul, hQrow, hφT]; rfl
    refine ⟨Qd * T, ?_, hSrow, ?_⟩
    · intro j i
      by_cases hj : j = j₀
      · subst hj; rw [hSrow i]; simp
      · have := hμ (j, i)
        rw [hQd, Matrix.mul_assoc, Matrix.diagonal_mul, if_neg hj]
        exact this
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc h.1, hhQ, Matrix.one_mul, hT]
