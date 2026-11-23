import Mathlib

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix
open scoped ComplexOrder

private theorem one_lt_re_det_one_add_and_im_eq_zero_of_posDef {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re ∧ ((1 + Q).det).im = 0 := by
  have hsp := hQ.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hQ.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Matrix.mem_unitaryGroup_iff.mp hQ.isHermitian.eigenvectorUnitary.2
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hQ.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hQ.eigenvalues_pos i
  rw [← hU, ← hd] at hsp

  have h1 : 1 + Q = U * (1 + diagonal (RCLike.ofReal ∘ d)) * star U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hsp]
  have hdet : (1 + Q).det = ((∏ i, (1 + d i) : ℝ) : ℂ) := by
    rw [h1, det_mul, det_mul, mul_comm U.det, mul_assoc, ← det_mul, hUU, det_one, mul_one,
      ← diagonal_one, diagonal_add, det_diagonal]
    push_cast
    rfl
  rw [hdet, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ < ∏ i, (1 + d i) := Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos)
        (fun i _ => by linarith [hdpos i]) Finset.univ_nonempty

theorem sc_one_add_det {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re := by
  exact (one_lt_re_det_one_add_and_im_eq_zero_of_posDef hQ).1

theorem sc_det_lt {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {E S : Matrix m m ℂ} (hE : E.PosDef) (hSE : (S - E).PosDef) :
    0 < (E.det).re ∧ (E.det).re < (S.det).re := by
  have hEdet := hE.det_pos
  rw [Complex.lt_def] at hEdet
  simp only [Complex.zero_re, Complex.zero_im] at hEdet

  have hsp := hE.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hE.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hE.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hE.eigenvalues_pos i
  rw [← hU, ← hd] at hsp
  obtain ⟨Dh, hDh⟩ : ∃ Dh : Matrix m m ℂ, Dh = diagonal (fun i => ((Real.sqrt (d i) : ℝ) : ℂ)) :=
    ⟨_, rfl⟩
  have hDD : Dh * Dh = diagonal (RCLike.ofReal ∘ d) := by
    rw [hDh, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdpos i).le]
    rfl
  have hDhH : Dhᴴ = Dh := by
    rw [hDh, diagonal_conjTranspose]
    congr 1
    funext i
    simp
  obtain ⟨B, hB⟩ : ∃ B : Matrix m m ℂ, B = Dh * star U := ⟨_, rfl⟩
  have hBB : Bᴴ * B = E := by
    rw [hB, conjTranspose_mul, hDhH, hsp, ← hDD]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hBdet : B.det ≠ 0 := by
    intro h0
    have h1 : E.det = 0 := by rw [← hBB, det_mul, h0, mul_zero]
    rw [h1] at hEdet
    simp at hEdet
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hinj : Function.Injective (B⁻¹).mulVec := by
    intro v w hvw
    have h := congrArg (fun z => B *ᵥ z) hvw
    simpa [mulVec_mulVec, mul_nonsing_inv B hBu] using h
  have hQ : ((B⁻¹)ᴴ * (S - E) * B⁻¹).PosDef := hSE.conjTranspose_mul_mul_same hinj
  have hS : Bᴴ * (1 + (B⁻¹)ᴴ * (S - E) * B⁻¹) * B = S := by
    have hinv : B⁻¹ * B = 1 := nonsing_inv_mul B hBu
    have e1 : Bᴴ * ((B⁻¹)ᴴ * (S - E) * B⁻¹) * B = (B⁻¹ * B)ᴴ * (S - E) * (B⁻¹ * B) := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB, e1, hinv, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
    abel
  generalize (B⁻¹)ᴴ * (S - E) * B⁻¹ = Q at hQ hS
  have hdet : S.det = (1 + Q).det * E.det := by
    rw [← hS, det_mul, det_mul, ← hBB, det_mul]
    ring
  obtain ⟨hq1, hq2⟩ := one_lt_re_det_one_add_and_im_eq_zero_of_posDef hQ
  refine ⟨hEdet.1, ?_⟩
  rw [hdet, Complex.mul_re, hq2, ← hEdet.2]
  nlinarith [hEdet.1, hq1]

theorem sc_schur_posDef {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    {A : Matrix k k ℂ} (B : Matrix k m ℂ) (D : Matrix m m ℂ) (hA : A.PosDef)
    (h : (fromBlocks A B Bᴴ D).PosDef) : (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨N, hN⟩ : ∃ N : Matrix (k ⊕ m) m ℂ, N = fromRows (-(A⁻¹ * B)) 1 := ⟨_, rfl⟩
  have hinj : Function.Injective N.mulVec := by
    intro v w hvw
    funext i
    have h1 := congrFun hvw (Sum.inr i)
    simpa [hN, fromRows_mulVec] using h1
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  have h1 : A * (-(A⁻¹ * B)) + B * (1 : Matrix m m ℂ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  have h2 : Bᴴ * (-(A⁻¹ * B)) + D * (1 : Matrix m m ℂ) = D - Bᴴ * A⁻¹ * B := by
    rw [Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc]
    abel
  have key : Nᴴ * fromBlocks A B Bᴴ D * N = D - Bᴴ * A⁻¹ * B := by
    rw [hN, conjTranspose_fromRows_eq_fromCols_conjTranspose, ← fromRows_fromCols_eq_fromBlocks,
      fromCols_mul_fromRows, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [fromCols_mul_fromRows, fromCols_mul_fromRows, h1, h2, Matrix.mul_zero, zero_add,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc]
  have hpd := h.conjTranspose_mul_mul_same hinj
  rwa [key] at hpd

theorem sc_quad_mul {r : Type*} [Fintype r] (H M : Matrix r r ℂ) (u : r → ℂ) :
    star u ⬝ᵥ ((Mᴴ * H * M) *ᵥ u) = star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u)) := by
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem sc_contr_posDef {r : Type*} [Fintype r] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re) :
    (H - Mᴴ * H * M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (hH.isHermitian.sub (isHermitian_conjTranspose_mul_mul M hH.isHermitian)) ?_
  intro x hx
  rw [sub_mulVec, dotProduct_sub, sc_quad_mul]
  have h1 : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := hH.isHermitian.im_star_dotProduct_mulVec_self x
  have h2 : (star (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x))).im = 0 :=
    hH.isHermitian.im_star_dotProduct_mulVec_self (M *ᵥ x)
  have h3 := hM x hx
  rw [Complex.lt_def, Complex.sub_re, Complex.sub_im, h1, h2, Complex.zero_re, Complex.zero_im]
  exact ⟨by linarith, by ring⟩

theorem sc_sigma {r k m : Type*} [Fintype r] [Fintype k] [Fintype m] [DecidableEq k]
    [DecidableEq m] [Nonempty m] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re)
    (Bm : Matrix r k ℂ) (Cm : Matrix r m ℂ) (hW : Function.Injective (fromCols Bm Cm).mulVec)
    (hMB : M * Bm = 0) (hMC : Function.Injective (M * Cm).mulVec) :
    0 < ((M * Cm)ᴴ * H * (M * Cm)).det.re ∧ ((M * Cm)ᴴ * H * (M * Cm)).det.re <
      (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)).det.re := by
  have hBinj : Function.Injective Bm.mulVec := by
    intro v w hvw
    have h : (fromCols Bm Cm) *ᵥ (Sum.elim v 0) = (fromCols Bm Cm) *ᵥ (Sum.elim w 0) := by
      rw [fromCols_mulVec, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inl,
        Sum.elim_comp_inr, Sum.elim_comp_inr, hvw]
    have h' := hW h
    funext i
    exact congrFun h' (Sum.inl i)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix k k ℂ, A = Bmᴴ * H * Bm := ⟨_, rfl⟩
  have hA : A.PosDef := by rw [hAdef]; exact hH.conjTranspose_mul_mul_same hBinj
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨G, hG⟩ : ∃ G : Matrix k m ℂ, G = A⁻¹ * (Bmᴴ * H * Cm) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix r m ℂ, N = Cm - Bm * G := ⟨_, rfl⟩
  have hNW : ∀ v, N *ᵥ v = (fromCols Bm Cm) *ᵥ (Sum.elim (-(G *ᵥ v)) v) := by
    intro v
    rw [hN, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_mulVec, mulVec_neg,
      mulVec_mulVec]
    abel
  have hNinj : Function.Injective N.mulVec := by
    intro v w hvw
    rw [hNW, hNW] at hvw
    have h := hW hvw
    funext i
    exact congrFun h (Sum.inr i)
  have hGA : A * G = Bmᴴ * H * Cm := by
    rw [hG, ← Matrix.mul_assoc, mul_nonsing_inv A hAu, Matrix.one_mul]
  have hx : Gᴴ * (Bmᴴ * (H * (Bm * G))) = Gᴴ * (Bmᴴ * (H * Cm)) := by
    have h := congrArg (fun X => Gᴴ * X) hGA
    simpa [hAdef, Matrix.mul_assoc] using h

  have key : Nᴴ * H * N = Cmᴴ * H * Cm - Cmᴴ * H * Bm * G := by
    rw [hN, conjTranspose_sub, conjTranspose_mul]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub]
    rw [hx]
    abel
  have hT : Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm) =
      Cmᴴ * H * Cm - Cmᴴ * H * Bm * G := by
    rw [hG, ← hAdef]
    simp only [Matrix.mul_assoc]
  have hMN : M * N = M * Cm := by
    rw [hN, Matrix.mul_sub, ← Matrix.mul_assoc, hMB, Matrix.zero_mul, sub_zero]
  have hdiff : (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)) -
      (M * Cm)ᴴ * H * (M * Cm) = Nᴴ * (H - Mᴴ * H * M) * N := by
    rw [hT, ← key, ← hMN, conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hpd := (sc_contr_posDef hH hM).conjTranspose_mul_mul_same hNinj
  refine sc_det_lt (hH.conjTranspose_mul_mul_same hMC) ?_
  rw [hdiff]
  exact hpd

end ReciprocityTheory.MultiplicativeHeights
