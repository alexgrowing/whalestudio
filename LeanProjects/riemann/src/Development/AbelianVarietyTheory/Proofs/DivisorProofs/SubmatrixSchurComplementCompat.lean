import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.HermFrame

open Matrix

section Summand

variable {m m' t l n : Type} [Fintype m] [Fintype m'] [Fintype t] [Fintype l]
  [DecidableEq m] [DecidableEq m'] [DecidableEq t] [DecidableEq l]

def summandMat (e : m' ⊕ t ≃ m) : Matrix m m' ℂ :=
  of fun p a => if p = e (Sum.inl a) then 1 else 0

theorem summandMat_mul_inl (e : m' ⊕ t ≃ m) (X : Matrix m' n ℂ) (a : m') (j : n) :
    (summandMat e * X) (e (Sum.inl a)) j = X a j := by
  simp [Matrix.mul_apply, summandMat]

theorem summandMat_mul_inr (e : m' ⊕ t ≃ m) (X : Matrix m' n ℂ) (b : t) (j : n) :
    (summandMat e * X) (e (Sum.inr b)) j = 0 := by
  simp [Matrix.mul_apply, summandMat]

theorem mul_summandMat (e : m' ⊕ t ≃ m) {k : Type} (Y : Matrix k m ℂ) (p : k) (a : m') :
    (Y * summandMat e) p a = Y p (e (Sum.inl a)) := by
  simp [Matrix.mul_apply, summandMat]

theorem summandMat_conjTranspose_mul (e : m' ⊕ t ≃ m) :
    (summandMat e)ᴴ * summandMat e = 1 := by
  ext a c
  rw [mul_summandMat]
  simp [summandMat, Matrix.one_apply, eq_comm]

theorem eq_summandMat_mul (e : m' ⊕ t ≃ m) {X : Matrix m n ℂ} {X' : Matrix m' n ℂ}
    (h1 : ∀ a j, X (e (Sum.inl a)) j = X' a j) (h2 : ∀ b j, X (e (Sum.inr b)) j = 0) :
    X = summandMat e * X' := by
  ext p j
  obtain ⟨q, rfl⟩ := e.surjective p
  rcases q with a | b
  · rw [summandMat_mul_inl, h1]
  · rw [summandMat_mul_inr, h2]

theorem inv_mul_eq_mul_inv_of_intertwine {A : Matrix m m ℂ} {A' : Matrix m' m' ℂ}
    {J : Matrix m m' ℂ} (hJ : Jᴴ * J = 1) (h : A * J = J * A') (hA : IsUnit A.det) :
    A⁻¹ * J = J * A'⁻¹ := by
  have hl : (Jᴴ * A⁻¹ * J) * A' = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc A⁻¹,
      nonsing_inv_mul _ hA, Matrix.one_mul, hJ]
  have hu : A' * A'⁻¹ = 1 := mul_nonsing_inv _ (isUnit_det_of_left_inverse hl)
  calc A⁻¹ * J = A⁻¹ * (J * (A' * A'⁻¹)) := by rw [hu, Matrix.mul_one]
    _ = A⁻¹ * (A * J * A'⁻¹) := by rw [h, Matrix.mul_assoc]
    _ = J * A'⁻¹ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, nonsing_inv_mul _ hA, Matrix.one_mul]

variable {e : m' ⊕ t ≃ m} {K : Matrix (m ⊕ l) (m ⊕ l) ℂ} {K' : Matrix (m' ⊕ l) (m' ⊕ l) ℂ}

theorem subGram_mul_summandMat
    (hK : K.submatrix (Sum.map (fun a => e (Sum.inl a)) id)
      (Sum.map (fun a => e (Sum.inl a)) id) = K')
    (h0 : ∀ (a : m' ⊕ l) (b : t), K (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧
      K (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0) :
    subGram K * summandMat e = summandMat e * subGram K' := by
  refine eq_summandMat_mul e (fun c a => ?_) fun b a => ?_
  · rw [mul_summandMat, ← hK]; rfl
  · rw [mul_summandMat]; exact (h0 (Sum.inl a) b).2

theorem subGram_transpose_mul_summandMat
    (hK : K.submatrix (Sum.map (fun a => e (Sum.inl a)) id)
      (Sum.map (fun a => e (Sum.inl a)) id) = K')
    (h0 : ∀ (a : m' ⊕ l) (b : t), K (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧
      K (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0) :
    (subGram K)ᵀ * summandMat e = summandMat e * (subGram K')ᵀ := by
  refine eq_summandMat_mul e (fun c a => ?_) fun b a => ?_
  · rw [mul_summandMat, ← hK]; rfl
  · rw [mul_summandMat]; exact (h0 (Sum.inl a) b).1

theorem quotGram_eq_of_summand
    (hK : K.submatrix (Sum.map (fun a => e (Sum.inl a)) id)
      (Sum.map (fun a => e (Sum.inl a)) id) = K')
    (h0 : ∀ (a : m' ⊕ l) (b : t), K (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧
      K (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0)
    (hu : IsUnit (subGram K).det) : quotGram K = quotGram K' := by
  have hA := inv_mul_eq_mul_inv_of_intertwine (summandMat_conjTranspose_mul e)
    (subGram_mul_summandMat hK h0) hu
  have hB : K.toBlocks₁₂ = summandMat e * K'.toBlocks₁₂ := by
    refine eq_summandMat_mul e (fun a j => ?_) fun b j => ?_
    · rw [← hK]; rfl
    · exact (h0 (Sum.inr j) b).2
  have hC : K.toBlocks₂₁ * summandMat e = K'.toBlocks₂₁ := by
    ext j a
    rw [mul_summandMat, ← hK]; rfl
  have hD : K.toBlocks₂₂ = K'.toBlocks₂₂ := by
    rw [← hK]; rfl
  have hA' : K.toBlocks₁₁⁻¹ * summandMat e = summandMat e * K'.toBlocks₁₁⁻¹ := hA
  have hm : K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ * K.toBlocks₁₂ =
      K'.toBlocks₂₁ * K'.toBlocks₁₁⁻¹ * K'.toBlocks₁₂ := by
    rw [hB, Matrix.mul_assoc, ← Matrix.mul_assoc K.toBlocks₁₁⁻¹, hA', ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hC, Matrix.mul_assoc]
  rw [quotGram, quotGram, hD, hm]

theorem orthCoeff_eq_of_summand
    (hK : K.submatrix (Sum.map (fun a => e (Sum.inl a)) id)
      (Sum.map (fun a => e (Sum.inl a)) id) = K')
    (h0 : ∀ (a : m' ⊕ l) (b : t), K (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧
      K (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0)
    (hu : IsUnit (subGram K).det) : orthCoeff K = summandMat e * orthCoeff K' := by
  have hu' : IsUnit (subGram K)ᵀ.det := by rwa [det_transpose]
  have hA : K.toBlocks₁₁ᵀ⁻¹ * summandMat e = summandMat e * K'.toBlocks₁₁ᵀ⁻¹ :=
    inv_mul_eq_mul_inv_of_intertwine (summandMat_conjTranspose_mul e)
      (subGram_transpose_mul_summandMat hK h0) hu'
  have hC : K.toBlocks₂₁ᵀ = summandMat e * K'.toBlocks₂₁ᵀ := by
    refine eq_summandMat_mul e (fun a j => ?_) fun b j => ?_
    · rw [← hK]; rfl
    · exact (h0 (Sum.inr j) b).1
  rw [orthCoeff, orthCoeff, hC, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

end Summand

section Forms

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
  {m m' t l : Type} [Fintype m] [Fintype m'] [Fintype t] [Fintype l]
  [DecidableEq m] [DecidableEq m'] [DecidableEq t] [DecidableEq l]

theorem extForm_eq_mdbar (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : V) :
    extForm H z η = mdbar (fun x => -orthCoeff (H x)) z η := by
  have h : mdbar (fun x => orthLift (H x)) z η =
      fromRows (mdbar (fun x => -orthCoeff (H x)) z η) 0 := by
    ext i j
    rcases i with a | b
    · simp only [mdbar_apply, orthLift, fromRows_apply_inl]
    · have h1 := congrFun (congrFun (mdbar_const (1 : Matrix l l ℂ) z η) b) j
      simpa only [mdbar_apply, orthLift, fromRows_apply_inr] using h1
  rw [extForm, h, orthProj, fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]

theorem mdbar_summandMat_mul (e : m' ⊕ t ≃ m) (X : V → Matrix m' l ℂ) (z η : V) :
    mdbar (fun x => summandMat e * X x) z η = summandMat e * mdbar X z η := by
  refine eq_summandMat_mul e (fun a j => ?_) fun b j => ?_
  · simp only [mdbar_apply, summandMat_mul_inl]
  · have h1 := congrFun (congrFun (mdbar_const (0 : Matrix m l ℂ) z η) (e (Sum.inr b))) j
    simpa only [mdbar_apply, summandMat_mul_inr, Matrix.zero_apply] using h1

theorem adj_mul_summandMat {A : Matrix m m ℂ} {A' : Matrix m' m' ℂ} {J : Matrix m m' ℂ}
    (hJ : Jᴴ * J = 1) (h : Aᵀ * J = J * A'ᵀ) (Q : Matrix l l ℂ) (b c : Matrix m' l ℂ) :
    adj Q A (J * b) * (J * c) = adj Q A' b * c := by
  rw [adj, adj, conjTranspose_mul]
  calc Qᵀ⁻¹ * (bᴴ * Jᴴ) * Aᵀ * (J * c) = Qᵀ⁻¹ * bᴴ * Jᴴ * (Aᵀ * J) * c := by
        simp only [Matrix.mul_assoc]
    _ = Qᵀ⁻¹ * bᴴ * (Jᴴ * J) * A'ᵀ * c := by
        rw [h]; simp only [Matrix.mul_assoc]
    _ = Qᵀ⁻¹ * bᴴ * A'ᵀ * c := by rw [hJ, Matrix.mul_one]

end Forms

theorem quotGram_extTrace_of_orthogonal_summand :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] (m m' t l : Type) [Fintype m] [Fintype m'] [Fintype t] [Fintype l] [DecidableEq m] [DecidableEq m'] [DecidableEq t] [DecidableEq l] (e : m' ⊕ t ≃ m), (∀ (K : Matrix (m ⊕ l) (m ⊕ l) ℂ) (K' : Matrix (m' ⊕ l) (m' ⊕ l) ℂ), K.submatrix (Sum.map (fun a => e (Sum.inl a)) id) (Sum.map (fun a => e (Sum.inl a)) id) = K' → (∀ (a : m' ⊕ l) (b : t), K (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧ K (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0) → IsUnit (GlobalTheory.HermFrame.subGram K).det → GlobalTheory.HermFrame.quotGram K = GlobalTheory.HermFrame.quotGram K') ∧ ∀ (K : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (K' : V → Matrix (m' ⊕ l) (m' ⊕ l) ℂ) (z : V), (∀ᶠ x in nhds z, (K x).submatrix (Sum.map (fun a => e (Sum.inl a)) id) (Sum.map (fun a => e (Sum.inl a)) id) = K' x ∧ (∀ (a : m' ⊕ l) (b : t), K x (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧ K x (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0) ∧ IsUnit (GlobalTheory.HermFrame.subGram (K x)).det) → GlobalTheory.HermFrame.extTrace K z = GlobalTheory.HermFrame.extTrace K' z := by
  intro V _ _ _ _ m m' t l _ _ _ _ _ _ _ _ e
  refine ⟨fun K K' hK h0 hu => quotGram_eq_of_summand hK h0 hu, fun K K' z h => ?_⟩
  obtain ⟨hK, h0, hu⟩ := h.self_of_nhds
  have hβ : ∀ η, extForm K z η = summandMat e * extForm K' z η := fun η => by
    rw [extForm_eq_mdbar, extForm_eq_mdbar, ← mdbar_summandMat_mul]
    refine mdbar_congr (h.mono fun x hx => ?_) η
    rw [orthCoeff_eq_of_summand hx.1 hx.2.1 hx.2.2, Matrix.mul_neg]
  funext ξ η
  rw [extTrace, extTrace, extFormAdj, extFormAdj, quotGram_eq_of_summand hK h0 hu, hβ, hβ,
    adj_mul_summandMat (summandMat_conjTranspose_mul e)
      (subGram_transpose_mul_summandMat hK h0)]

end GlobalTheory.HermFrame
