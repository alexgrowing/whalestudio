import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder
open Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.RL.Frame

theorem quad_diag {α : Type} [Fintype α] [DecidableEq α] (d : α → ℝ) (v : α → ℂ) :
    star v ⬝ᵥ (Matrix.diagonal (fun a => (d a : ℂ))) *ᵥ v = ((∑ a, d a * Complex.normSq (v a) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_diagonal, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  simp only [Pi.star_apply, RCLike.star_def]
  ring

theorem inertia_le {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (d : α → ℝ) (e : β → ℝ)
    (G : Matrix β α ℂ) (h : Gᴴ * Matrix.diagonal (fun b => (e b : ℂ)) * G = Matrix.diagonal (fun a => (d a : ℂ))) :
    Fintype.card {a // 0 < d a} ≤ Fintype.card {b // 0 < e b} := by
  classical
  let ext : ({a // 0 < d a} → ℂ) →ₗ[ℂ] (α → ℂ) :=
    { toFun := fun v a => if h : 0 < d a then v ⟨a, h⟩ else 0
      map_add' := by
        intro v w; funext a; by_cases h : 0 < d a <;> simp [h]
      map_smul' := by
        intro c v; funext a; by_cases h : 0 < d a <;> simp [h] }
  let f : ({a // 0 < d a} → ℂ) →ₗ[ℂ] ({b // 0 < e b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Subtype.val) ∘ₗ G.mulVecLin ∘ₗ ext
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hw : ∀ b, 0 < e b → (G *ᵥ ext v) b = 0 := fun b hb => congrFun hv ⟨b, hb⟩
    have h1 : star (ext v) ⬝ᵥ (Matrix.diagonal (fun a => (d a : ℂ))) *ᵥ ext v =
        star (G *ᵥ ext v) ⬝ᵥ (Matrix.diagonal (fun b => (e b : ℂ))) *ᵥ (G *ᵥ ext v) := by
      rw [← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [quad_diag, quad_diag, Complex.ofReal_inj] at h1
    have h2 : ∑ b, e b * Complex.normSq ((G *ᵥ ext v) b) ≤ 0 := by
      refine Finset.sum_nonpos fun b _ => ?_
      by_cases hb : 0 < e b
      · simp [hw b hb]
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hb) (Complex.normSq_nonneg _)
    have h3 : ∀ a ∈ Finset.univ, 0 ≤ d a * Complex.normSq (ext v a) := by
      intro a _
      by_cases ha : 0 < d a
      · exact mul_nonneg ha.le (Complex.normSq_nonneg _)
      · simp [ext, ha]
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg h3).mp (le_antisymm (h1 ▸ h2) (Finset.sum_nonneg h3))
    funext a
    have h5 := h4 a.1 (Finset.mem_univ _)
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 a.2.ne'
    · have h7 := Complex.normSq_eq_zero.mp h6
      simpa [ext, a.2] using h7
  simpa using LinearMap.finrank_le_finrank_of_injective hf

def sg (r s : ℕ) : Fin r ⊕ Fin s → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem blocks_eq (r s : ℕ) :
    (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) = Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
  ext (i | i) (j | j) <;> simp [sg, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_eq (r s : ℕ) : Jm r s = Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
  rw [← blocks_eq]; rfl

theorem sg_sq (r s : ℕ) :
    Matrix.diagonal (fun a => (sg r s a : ℂ)) * Matrix.diagonal (fun a => (sg r s a : ℂ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases a with a | a <;> simp [sg]

theorem card_pos (r s : ℕ) : Fintype.card {a // 0 < sg r s a} ≤ r := by
  have hs : Function.Surjective (fun a : Fin r => (⟨Sum.inl a, by simp [sg]⟩ : {a // 0 < sg r s a})) := by
    rintro ⟨a | a, ha⟩
    · exact ⟨a, rfl⟩
    · simp [sg] at ha; linarith
  simpa using Fintype.card_le_of_surjective _ hs

theorem card_neg (r s : ℕ) : Fintype.card {a // 0 < -sg r s a} ≤ s := by
  have hs : Function.Surjective (fun a : Fin s => (⟨Sum.inr a, by simp [sg]⟩ : {a // 0 < -sg r s a})) := by
    rintro ⟨a | a, ha⟩
    · simp [sg] at ha; linarith
    · exact ⟨a, rfl⟩
  simpa using Fintype.card_le_of_surjective _ hs

theorem diag_ex {n : ℕ} (M φ : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (hφ : φ * φ = 1) (hN : (M * φ).PosDef) :
    ∃ (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i = 1 ∨ d i = -1) ∧
      Cᴴ * M * C = Matrix.diagonal (fun i => (d i : ℂ)) ∧ φ * C = C * Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨P, hP, hPN⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hN.isStrictlyPositive
  obtain ⟨Q, hPQ, hQP⟩ : ∃ Q, P * Q = 1 ∧ Q * P = 1 := by
    obtain ⟨u, rfl⟩ := hP
    exact ⟨↑u⁻¹, u.mul_inv, u.inv_mul⟩
  have hK : (Qᴴ * M * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hM
  have hMe : M = Pᴴ * P * φ := by
    rw [← Matrix.star_eq_conjTranspose, ← hPN, Matrix.mul_assoc, hφ, Matrix.mul_one]
  have hKe : Qᴴ * M * Q = P * φ * Q := by
    have h1 : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    conv_lhs => rw [hMe]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  set U : Matrix (Fin n) (Fin n) ℂ := hK.eigenvectorUnitary.1 with hU
  have hU1 : star U * U = 1 := hK.eigenvectorUnitary.2.1
  have hU2 : U * star U = 1 := hK.eigenvectorUnitary.2.2
  have hD : star U * (Qᴴ * M * Q) * U = Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ)) := by
    have := hK.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    rw [Unitary.coe_star, star_star] at this
    exact this
  have hφC : φ * (Q * U) = Q * U * Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ)) := by
    rw [← hD, hKe]
    calc φ * (Q * U) = (Q * (U * star U) * P) * φ * (Q * U) := by
          rw [hU2, Matrix.mul_one, hQP, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨Q * U, hK.eigenvalues, ?_, ?_, hφC⟩
  · have hsq : Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ)) * Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ)) = 1 := by
      rw [← hD, hKe]
      calc star U * (P * φ * Q) * U * (star U * (P * φ * Q) * U)
          = star U * (P * (φ * (Q * (U * star U) * P) * φ) * Q) * U := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hU2, Matrix.mul_one, hQP, Matrix.mul_one, hφ, Matrix.mul_one, hPQ, Matrix.mul_one, hU1]
    intro i
    have h1 := congrFun (congrFun hsq i) i
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
    have h2 : hK.eigenvalues i * hK.eigenvalues i = 1 := by exact_mod_cast h1
    exact mul_self_eq_one_iff.mp h2
  · rw [← hD, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]

theorem frame_conj {n r s : ℕ} (hn : r + s = n) (M φ : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ)
    (hB : Bᴴ * M * B = Matrix.diagonal (fun a => (sg r s a : ℂ))) (hφ : φ * φ = 1) (hiso : φᴴ * M * φ = M)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (φᴴ * M) *ᵥ x).re) :
    ∃ C : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ, Cᴴ * M * C = Matrix.diagonal (fun a => (sg r s a : ℂ)) ∧
      (∃ C' : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ, C * C' = 1) ∧ φ * C = C * Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
  classical
  have hcard : Fintype.card (Fin r ⊕ Fin s) = Fintype.card (Fin n) := by simp [hn]
  have hinv : ∀ C : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ, Cᴴ * M * C = Matrix.diagonal (fun a => (sg r s a : ℂ)) →
      ∃ C' : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ, C * C' = 1 := by
    intro C hC
    refine ⟨Matrix.diagonal (fun a => (sg r s a : ℂ)) * Cᴴ * M, ?_⟩
    rw [← Matrix.mul_eq_one_comm_of_card_eq _ _ _ hcard]
    calc _ = Matrix.diagonal (fun a => (sg r s a : ℂ)) * (Cᴴ * M * C) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hC, sg_sq]
  obtain ⟨B', hB'⟩ := hinv B hB
  have hMe : M = B'ᴴ * Matrix.diagonal (fun a => (sg r s a : ℂ)) * B' := by
    rw [← hB]
    calc M = (B * B')ᴴ * M * (B * B') := by rw [hB', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hM : M.IsHermitian := by
    rw [hMe]
    refine Matrix.isHermitian_conjTranspose_mul_mul _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro a
    simp [IsSelfAdjoint]
  have hN : φᴴ * M = M * φ := by
    calc φᴴ * M = φᴴ * M * (φ * φ) := by rw [hφ, Matrix.mul_one]
      _ = M * φ := by rw [← Matrix.mul_assoc, hiso]
  have hNH : (M * φ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hM.eq, hN]
  have hPD : (M * φ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hNH fun x hx => ?_
    have h1 := hpos x hx
    rw [hN] at h1
    rw [Complex.pos_iff]
    refine ⟨h1, ?_⟩
    have h2 := hNH.im_star_dotProduct_mulVec_self x
    simpa using h2.symm
  obtain ⟨C, d, hd, hC, hφC⟩ := diag_ex M φ hM hφ hPD
  have hG : (B' * C)ᴴ * Matrix.diagonal (fun a => (sg r s a : ℂ)) * (B' * C) = Matrix.diagonal (fun i => (d i : ℂ)) := by
    rw [← hC, Matrix.conjTranspose_mul]
    conv_rhs => rw [hMe]
    simp only [Matrix.mul_assoc]
  have hp : Fintype.card {i // 0 < d i} ≤ r := (inertia_le d _ _ hG).trans (card_pos r s)
  have hG' : (B' * C)ᴴ * Matrix.diagonal (fun a => ((-sg r s a : ℝ) : ℂ)) * (B' * C) =
      Matrix.diagonal (fun i => ((-d i : ℝ) : ℂ)) := by
    have e1 : Matrix.diagonal (fun a => ((-sg r s a : ℝ) : ℂ)) = -Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
      rw [Matrix.diagonal_neg]; simp
    have e2 : Matrix.diagonal (fun i => ((-d i : ℝ) : ℂ)) = -Matrix.diagonal (fun i => (d i : ℂ)) := by
      rw [Matrix.diagonal_neg]; simp
    rw [e1, e2, Matrix.mul_neg, Matrix.neg_mul, hG]
  have hq0 : Fintype.card {i // 0 < -d i} ≤ s := (inertia_le (fun i => -d i) (fun a => -sg r s a) _ hG').trans (card_neg r s)
  have hq : Fintype.card {i // ¬ 0 < d i} ≤ s := by
    refine le_trans (le_of_eq (Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_))) hq0
    rcases hd i with h | h <;> simp [h]
  have hsum : Fintype.card {i // 0 < d i} + Fintype.card {i // ¬ 0 < d i} = n := by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => 0 < d i), Fintype.card_fin]
  have hp' : Fintype.card (Fin r) = Fintype.card {i // 0 < d i} := by rw [Fintype.card_fin]; omega
  have hq' : Fintype.card (Fin s) = Fintype.card {i // ¬ 0 < d i} := by rw [Fintype.card_fin]; omega
  let e : Fin r ⊕ Fin s ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivOfCardEq hp') (Fintype.equivOfCardEq hq')).trans (Equiv.sumCompl fun i => 0 < d i)
  have he : ∀ a, d (e a) = sg r s a := by
    rintro (a | a)
    · have h1 : 0 < d (e (.inl a)) := (Fintype.equivOfCardEq hp' a).2
      rcases hd (e (.inl a)) with h | h
      · simpa [sg] using h
      · rw [h] at h1; linarith
    · have h1 : ¬ 0 < d (e (.inr a)) := (Fintype.equivOfCardEq hq' a).2
      rcases hd (e (.inr a)) with h | h
      · rw [h] at h1; simp at h1
      · simpa [sg] using h
  have hde : (Matrix.diagonal (fun i => (d i : ℂ))).submatrix e e = Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    simp [he]
  have hC2 : (C.submatrix id e)ᴴ * M * C.submatrix id e = Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
    rw [← hde, ← hC]
    ext a b
    simp [Matrix.mul_apply]
  refine ⟨C.submatrix id e, hC2, hinv _ hC2, ?_⟩
  ext i a
  have h1 := congrFun (congrFun hφC i) (e a)
  rw [Matrix.mul_diagonal] at h1 ⊢
  rw [← he]
  exact h1

end PositivityTheory.RL.Frame

namespace PositivityTheory.RL

open _root_.PositivityTheory.RL.Frame

theorem frameEx : GlobalTheory.RealLift.FrameEx := by
  rintro n r s M θ ⟨hn, B, hB⟩ ⟨hθ, hiso, hpos⟩
  have ct : ∀ {α β : Type} (X : Matrix α β ℂ), (X.map star)ᴴ = Xᵀ := by
    intro α β X; ext i j; simp
  have mm : ∀ {α β : Type} (X : Matrix α β ℂ), (X.map star).map star = X := by
    intro α β X; ext i j; simp
  have mul : ∀ {α β γ : Type} [Fintype β] (X : Matrix α β ℂ) (Y : Matrix β γ ℂ),
      (X * Y).map star = X.map star * Y.map star := by
    intro α β γ _ X Y
    exact Matrix.map_mul (f := starRingEnd ℂ)
  have one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 := Matrix.map_one _ (star_zero _) (star_one _)
  obtain ⟨C, hC, ⟨C', hC'⟩, hφ⟩ := frame_conj hn M (θ.map star) (B.map star) (by rw [ct, hB, blocks_eq])
    (by rw [← mul, hθ, one]) (by rw [ct, hiso]) (by
      intro x hx
      have h1 := hpos (star x) (by simpa using hx)
      rw [star_star, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] at h1
      rw [ct]
      exact h1)
  refine ⟨C.map star, ⟨?_, C'.map star, ?_⟩, ?_⟩
  · rw [← ct, mm, hC, Jm_eq]
  · rw [← mul, hC', one]
  · have h1 := congrArg (fun X => Matrix.map X star) hφ
    simp only [mul, mm] at h1
    rw [h1, Jm_eq]
    congr 1
    ext a b
    by_cases h : a = b <;> simp [h]

end PositivityTheory.RL
