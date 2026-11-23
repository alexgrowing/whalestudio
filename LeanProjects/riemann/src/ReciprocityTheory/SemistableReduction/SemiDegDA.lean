import ReciprocityTheory.SemistableReduction.SemiDegSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem sdd_quad_conj {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin m → ℂ) :
    star w ⬝ᵥ ((Pᴴ * Q * P) *ᵥ w) = star (P *ᵥ w) ⬝ᵥ (Q *ᵥ (P *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem sdd_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, A = Bᴴ * B ∧ IsUnit B.det := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)
  refine ⟨B, hB, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hp := hA.det_pos
  rw [hB, star_eq_conjTranspose, det_mul, h0, mul_zero] at hp
  exact lt_irrefl _ hp

theorem sdd_star_self_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (⇑(hD.eigenvectorBasis i)) = 1 := by
  have h := orthonormal_iff_ite.mp hD.eigenvectorBasis.orthonormal i i
  rw [if_pos rfl, PiLp.inner_apply] at h
  rw [← h]
  simp only [dotProduct, Pi.star_apply, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.star_def, mul_comm]

theorem sdd_quad_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (D *ᵥ ⇑(hD.eigenvectorBasis i)) = (hD.eigenvalues i : ℂ) := by
  rw [hD.mulVec_eigenvectorBasis, dotProduct_smul, sdd_star_self_eig hD i]
  simp

theorem sdd_det_abs_le_one {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, ‖star w ⬝ᵥ (D *ᵥ w)‖ ≤ (star w ⬝ᵥ w).re) : ‖D.det‖ ≤ 1 := by
  rw [hD.det_eq_prod_eigenvalues, norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i _
  have hi := h (hD.eigenvectorBasis i)
  rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re] at hi

theorem sdd_det_ge_one {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (D *ᵥ w)).re) :
    D.det = ((D.det.re : ℝ) : ℂ) ∧ 1 ≤ D.det.re := by
  have hev : ∀ i, 1 ≤ hD.eigenvalues i := by
    intro i
    have hi := h (hD.eigenvectorBasis i)
    rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re, Complex.ofReal_re] at hi
  have hdet : D.det = ((∏ i, hD.eigenvalues i : ℝ) : ℂ) := by
    rw [hD.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rfl
  rw [hdet, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hev i)

theorem sdd_congr {n : ℕ} (B X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) :
    X = Bᴴ * ((B⁻¹)ᴴ * X * B⁻¹) * B ∧
    ∀ w : Fin n → ℂ, star w ⬝ᵥ (((B⁻¹)ᴴ * X * B⁻¹) *ᵥ w) =
      star (B⁻¹ *ᵥ w) ⬝ᵥ (X *ᵥ (B⁻¹ *ᵥ w)) := by
  refine ⟨?_, fun w => sdd_quad_conj B⁻¹ X w⟩
  have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have h2 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  calc X = (Bᴴ * (B⁻¹)ᴴ) * X * (B⁻¹ * B) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sdd_quad_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) (w : Fin n → ℂ) :
    star w ⬝ᵥ w = star (B⁻¹ *ᵥ w) ⬝ᵥ ((Bᴴ * B) *ᵥ (B⁻¹ *ᵥ w)) := by
  have hw : B *ᵥ (B⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have e := sdd_quad_conj B 1 (B⁻¹ *ᵥ w)
  rw [Matrix.mul_one, hw, Matrix.one_mulVec] at e
  exact e.symm

theorem sdd_norm_det_sq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem sdd_det_congr {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * D * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) * D.det := by
  rw [det_mul, det_mul, ← sdd_norm_det_sq B, det_mul]
  ring

theorem sdd_absDet {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.IsHermitian)
    (h : ∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) :
    ‖C.det‖ ≤ A.det.re := by
  obtain ⟨B, hAB, hu⟩ := sdd_factor hA
  obtain ⟨hCe, hq⟩ := sdd_congr B C hu
  have hDh : ((B⁻¹)ᴴ * C * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hC.eq, Matrix.mul_assoc]
  have hD1 : ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ 1 := by
    apply sdd_det_abs_le_one hDh
    intro w
    rw [hq w, sdd_quad_self B hu w, ← hAB]
    exact h _
  have hdetA : A.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hAB, sdd_norm_det_sq]
  rw [hCe, sdd_det_congr, hdetA, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖B.det‖ ^ 2 * ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ ‖B.det‖ ^ 2 * 1 := by gcongr
    _ = _ := mul_one _

theorem sdd_det_mono {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).re ≤ (star v ⬝ᵥ (Y *ᵥ v)).re) :
    0 < X.det.re ∧ X.det.re ≤ Y.det.re := by
  obtain ⟨B, hXB, hu⟩ := sdd_factor hX
  obtain ⟨hYe, hq⟩ := sdd_congr B Y hu
  have hDh : ((B⁻¹)ᴴ * Y * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hY.eq, Matrix.mul_assoc]
  obtain ⟨hDr, hD1⟩ := sdd_det_ge_one hDh (fun w => by
    rw [hq w, sdd_quad_self B hu w, ← hXB]
    exact h _)
  have hdetX : X.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hXB, sdd_norm_det_sq]
  have hBpos : 0 < ‖B.det‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu.ne_zero) 2
  rw [hdetX, hYe, sdd_det_congr, hDr, Complex.ofReal_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact ⟨hBpos, le_mul_of_one_le_right hBpos.le hD1⟩

def embM {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l i => σ (b i l)

theorem sdd_gramX_eq {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    gramX H σ b c = (embM σ b)ᴴ * H * embM σ c := by
  ext i j
  simp only [gramX, embM, embVec, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sdd_gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embM σ b)ᴴ * H * embM σ b := sdd_gramX_eq H σ b b

theorem sdd_embM_inj {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) : Function.Injective (embM σ b).mulVec := by
  classical
  let M : Matrix (Fin r) (Fin k) K := Matrix.of fun l i => b i l
  have hM : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hs : ∑ i, x i • b i = M.mulVecLin x := by
      ext l
      simp [M, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply]
    rw [hx] at hs
    exact funext (Fintype.linearIndependent_iff.mp hb x hs)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.mpr hM)
  have hLM : LinearMap.toMatrix' g * M = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hg x
  have hE : embM σ b = M.map σ := rfl
  intro x y hxy
  have e := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simp only [hE, Matrix.mulVec_mulVec, ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.one_mulVec] at e
  exact e

theorem sdd_diag_quad {r : ℕ} (d : Fin r → ℝ) (x : Fin r → ℂ) :
    (star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x)).re = ∑ l, d l * ‖x l‖ ^ 2 := by
  have e : star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x) = ∑ l, ((d l * ‖x l‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, ← mul_assoc, mul_comm ((starRingEnd ℂ) (x l)), mul_assoc, Complex.conj_mul']
    push_cast
    ring
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem sdd_cut_quad {r k : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 ≤ d l) (e : ℕ)
    (E B1 : Matrix (Fin r) (Fin k) ℂ) (hB1 : ∀ l j, B1 l j = if e ≤ (l : ℕ) then E l j else 0)
    (v : Fin k → ℂ) :
    (star v ⬝ᵥ ((B1ᴴ * diagonal (fun l => (d l : ℂ)) * B1) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * diagonal (fun l => (d l : ℂ)) * E) *ᵥ v)).re := by
  rw [sdd_quad_conj, sdd_quad_conj, sdd_diag_quad, sdd_diag_quad]
  refine Finset.sum_le_sum fun l _ => ?_
  have hrow : (B1 *ᵥ v) l = if e ≤ (l : ℕ) then (E *ᵥ v) l else 0 := by
    by_cases hc : e ≤ (l : ℕ) <;> simp [Matrix.mulVec, dotProduct, hB1, hc]
  rw [hrow]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    nlinarith [hd l, sq_nonneg ‖(E *ᵥ v) l‖]

theorem sdd_schur {r k₀ k₁ : ℕ} (B : Matrix (Fin r) (Fin k₀) ℂ) (C : Matrix (Fin r) (Fin k₁) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : Hᴴ = H) (hG : (Bᴴ * H * B).IsHermitian)
    (hu : IsUnit (Bᴴ * H * B).det) :
    Cᴴ * H * C - (Cᴴ * H * B) * (Bᴴ * H * B)⁻¹ * (Bᴴ * H * C) =
      (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C)))ᴴ * H *
        (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C))) := by
  set G := Bᴴ * H * B with hGdef
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hGinvH : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG.eq]
  have hYH : (Bᴴ * H * C)ᴴ = Cᴴ * H * B := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  have hXh : (G⁻¹ * (Bᴴ * H * C))ᴴ = (Cᴴ * H * B) * G⁻¹ := by
    rw [conjTranspose_mul, hYH, hGinvH]
  have hcanc : ∀ Z : Matrix (Fin k₀) (Fin k₁) ℂ, G⁻¹ * (Bᴴ * (H * (B * Z))) = Z := by
    intro Z
    have hz : Bᴴ * (H * (B * Z)) = G * Z := by simp only [hGdef, Matrix.mul_assoc]
    rw [hz, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
  rw [conjTranspose_sub, conjTranspose_mul, hXh]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hcanc]
  abel

end ReciprocityTheory.MultiplicativeHeights
