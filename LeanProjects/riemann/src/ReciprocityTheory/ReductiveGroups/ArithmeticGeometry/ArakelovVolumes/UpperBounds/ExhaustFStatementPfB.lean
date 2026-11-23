import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem neg_of_perp' {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) {e : Fin r → ℂ}
    (he : e ≠ 0) (hperp : ∀ b, hermC τ.1 X.Gm e (X.colP x τ b) = 0) :
    (hermC τ.1 X.Gm e e).re < 0 := by
  classical
  obtain ⟨P, hPdet, hPgram⟩ := X.signature τ
  have hG := X.Gm_herm
  have hg : ∀ a b, hermC τ.1 X.Gm (FD.col P a) (FD.col P b) =
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 a : ℝ) : ℂ)) a b := fun a b => by
    rw [← hPgram]; rfl
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hPdet
  have hcoord : ∀ u : Fin r → ℂ, ∑ a, (P⁻¹ *ᵥ u) a • FD.col P a = u := by
    intro u
    have h1 : P *ᵥ (P⁻¹ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    conv_rhs => rw [← h1]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD.col, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hquad : ∀ y : Fin r → ℂ, hermC τ.1 X.Gm (∑ a, y a • FD.col P a) (∑ b, y b • FD.col P b) =
      ∑ a, y a * conj (y a) * ((sgn X.p0 a : ℝ) : ℂ) := by
    intro y
    rw [hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_left, hermC_sum_right]
    simp_rw [hermC_smul_right, hg, Matrix.diagonal_apply]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  by_contra hcon
  push_neg at hcon
  let Q : Matrix (Fin r) (Option (Fin X.p0)) ℂ :=
    fun k o => Option.elim o (e k) (fun b => X.colP x τ b k)
  let R : Matrix (Fin X.p0) (Option (Fin X.p0)) ℂ := (P⁻¹ * Q).submatrix (Fin.castLE X.p0_le) id
  have hker : LinearMap.ker (Matrix.mulVecLin R) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
  have hQv : Q *ᵥ z = ∑ b, z (some b) • X.colP x τ b + z none • e := by
    funext k
    simp only [Q, Matrix.mulVec, dotProduct, Fintype.sum_option, Option.elim, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    · exact mul_comm _ _
  have hy0 : ∀ a : Fin X.p0,
      (P⁻¹ *ᵥ (∑ b, z (some b) • X.colP x τ b + z none • e)) (Fin.castLE X.p0_le a) = 0 := by
    intro a
    have h3 : ((P⁻¹ * Q) *ᵥ z) (Fin.castLE X.p0_le a) = 0 := congrFun hz a
    rwa [← Matrix.mulVec_mulVec, hQv] at h3
  set w : Fin r → ℂ := ∑ b, z (some b) • X.colP x τ b with hwdef
  set v : Fin r → ℂ := w + z none • e with hvdef
  set y : Fin r → ℂ := P⁻¹ *ᵥ v with hydef
  have hvP : v = ∑ k, y k • FD.col P k := (hcoord v).symm
  have hsg : ∀ k, y k * conj (y k) * ((sgn X.p0 k : ℝ) : ℂ) =
      -((Complex.normSq (y k) : ℝ) : ℂ) := by
    intro k
    by_cases hk : (k : ℕ) < X.p0
    · have : y k = 0 := hy0 ⟨k, hk⟩
      simp [this]
    · simp [sgn, hk, Complex.mul_conj]
  have hvv1 : hermC τ.1 X.Gm v v = -∑ k, ((Complex.normSq (y k) : ℝ) : ℂ) := by
    rw [hvP, hquad]
    simp only [hsg, Finset.sum_neg_distrib]
  have hwe : hermC τ.1 X.Gm w e = 0 := by
    rw [hwdef, hermC_sum_left]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hermC_smul_left, ← hermC_conj τ.1 hG, hperp b, map_zero, mul_zero]
  have hew : hermC τ.1 X.Gm e w = 0 := by
    rw [hwdef, hermC_sum_right]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hermC_smul_right, hperp b, mul_zero]
  have hvv2 : hermC τ.1 X.Gm v v =
      hermC τ.1 X.Gm w w + z none * conj (z none) * hermC τ.1 X.Gm e e := by
    rw [hvdef]
    simp only [hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hwe, hew]
    ring
  have hwq : hermC τ.1 X.Gm w w =
      ∑ a, ∑ b, z (some a) * X.gramPos x τ a b * conj (z (some b)) := by
    rw [hwdef, hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hermC_smul_right, Data.gramPos_apply]
    ring
  have hre : (hermC τ.1 X.Gm v v).re =
      (hermC τ.1 X.Gm w w).re + Complex.normSq (z none) * (hermC τ.1 X.Gm e e).re := by
    rw [hvv2, Complex.mul_conj, Complex.add_re, Complex.re_ofReal_mul]
  have hre2 : (hermC τ.1 X.Gm v v).re = -∑ k, Complex.normSq (y k) := by
    rw [hvv1]; simp
  have hww : 0 ≤ (hermC τ.1 X.Gm w w).re := by
    by_cases hz1 : (fun b => z (some b)) = 0
    · have hw0 : w = 0 := by
        rw [hwdef]
        simp [show ∀ b, z (some b) = 0 from fun b => congrFun hz1 b]
      rw [hw0]; simp [hermC]
    · rw [hwq]; exact (quad_re_pos hA hz1).le
  have hnn : 0 ≤ (hermC τ.1 X.Gm v v).re := by
    rw [hre]; exact add_nonneg hww (mul_nonneg (Complex.normSq_nonneg _) hcon)
  have hy : ∀ k, y k = 0 := by
    have hs : ∑ k, Complex.normSq (y k) = 0 := by
      have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (y k))
      rw [hre2] at hnn
      linarith
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (y k))).1 hs k
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hv0 : v = 0 := by
    rw [hvP]; simp [hy]
  have hzs : (fun b => z (some b)) = 0 := by
    by_contra hz1
    have h1 := quad_re_pos hA hz1
    rw [← hwq] at h1
    have h0 : (hermC τ.1 X.Gm v v).re = 0 := by rw [hv0]; simp [hermC]
    rw [hre] at h0
    nlinarith [mul_nonneg (Complex.normSq_nonneg (z none)) hcon]
  have hw0 : w = 0 := by
    rw [hwdef]
    simp [show ∀ b, z (some b) = 0 from fun b => congrFun hzs b]
  have ht0 : z none = 0 := by
    have h := hv0
    rw [hvdef, hw0, zero_add] at h
    exact (smul_eq_zero.1 h).resolve_right he
  apply hz0
  funext o
  cases o with
  | none => exact ht0
  | some b => exact congrFun hzs b

theorem psgn_dmin_gt {x : Frame X.Ψ r} (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (hA : (X.gramPos x τ).PosDef) (k : ℕ) (hk : X.p0 + k ≤ r) (i : Fin (r + 1))
    (hik : (i : ℕ) = X.p0 + k) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  classical
  have hG := X.Gm_herm
  let gr : Fin k → Fin r := fun j => ⟨X.p0 + j, by have := j.isLt; omega⟩
  let d : Fin k → Fin r → ℂ := fun j => FD.col (mat x τ) (gr j)
  let A : Matrix (Fin X.p0) (Fin X.p0) ℂ := X.gramPos x τ
  let B : Matrix (Fin X.p0) (Fin k) ℂ := fun a l => hermC τ.1 X.Gm (X.colP x τ a) (d l)
  let C : Matrix (Fin k) (Fin X.p0) ℂ := fun j b => hermC τ.1 X.Gm (d j) (X.colP x τ b)
  let D : Matrix (Fin k) (Fin k) ℂ := fun j l => hermC τ.1 X.Gm (d j) (d l)
  have hApos : 0 < A.det := Matrix.PosDef.det_pos hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hApos.ne'
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hAu
  have hdm : dmin X.Gm x τ i = (Matrix.fromBlocks A B C D).det := by
    let e : Fin X.p0 ⊕ Fin k ≃ Fin (i : ℕ) := finSumFinEquiv.trans (finCongr hik.symm)
    unfold dmin lminor
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext s t
    rcases s with a | j <;> rcases t with b | l <;> rfl
  rw [hdm, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  set α : Matrix (Fin k) (Fin X.p0) ℂ := C * A⁻¹ with hαdef
  have hαA : α * A = C := by
    rw [hαdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
  have hAab : ∀ a b, A a b = hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) := fun a b => by
    show X.gramPos x τ a b = _
    rw [Data.gramPos_apply]
  let wv : Fin k → Fin r → ℂ := fun j => d j + ∑ a, (-α j a) • X.colP x τ a
  have hwc : ∀ j b, hermC τ.1 X.Gm (wv j) (X.colP x τ b) = 0 := by
    intro j b
    show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (X.colP x τ b) = 0
    rw [hermC_add_left, hermC_sum_left]
    simp only [hermC_smul_left]
    have h1 : ∑ a, -α j a * hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = -(α * A) j b := by
      rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hAab]
      ring
    rw [h1, hαA]
    exact add_neg_cancel _
  have hSw : ∀ j l, (D - α * B) j l = hermC τ.1 X.Gm (wv j) (wv l) := by
    intro j l
    have h2 : hermC τ.1 X.Gm (wv j) (wv l) = hermC τ.1 X.Gm (wv j) (d l) := by
      show hermC τ.1 X.Gm (wv j) (d l + ∑ a, (-α l a) • X.colP x τ a) = _
      rw [hermC_add_right, hermC_sum_right]
      simp only [hermC_smul_right, hwc, mul_zero, Finset.sum_const_zero, add_zero]
    have h3 : hermC τ.1 X.Gm (wv j) (d l) = D j l - (α * B) j l := by
      show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (d l) = _
      rw [hermC_add_left, hermC_sum_left, Matrix.mul_apply, sub_eq_add_neg,
        ← Finset.sum_neg_distrib]
      simp only [hermC_smul_left]
      congr 1
      exact Finset.sum_congr rfl fun a _ => neg_mul _ _
    rw [Matrix.sub_apply, h2, h3]
  have hSH : (D - α * B).IsHermitian := Matrix.IsHermitian.ext fun j l => by
    rw [hSw, hSw]
    exact hermC_conj τ.1 hG _ _
  have hli0 : LinearIndependent ℂ (fun m => FD.col (mat x τ) m) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hg : Function.Injective (Sum.elim (Fin.castLE X.p0_le) gr) := by
    intro s t hst
    rcases s with a | j <;> rcases t with b | l
    · exact congrArg Sum.inl (Fin.castLE_injective X.p0_le hst)
    · exfalso
      have h1 := congrArg Fin.val hst
      have := a.isLt
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      omega
    · exfalso
      have h1 := congrArg Fin.val hst
      have := b.isLt
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      omega
    · have h1 := congrArg Fin.val hst
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hli := hli0.comp _ hg
  have hS : (-(D - α * B)).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hSH.neg fun xv hxv => ?_
    set W : Fin r → ℂ := ∑ j, conj (xv j) • wv j with hWdef
    have hq : star xv ⬝ᵥ ((-(D - α * B)) *ᵥ xv) = -hermC τ.1 X.Gm W W := by
      rw [hWdef, hermC_sum_left]
      simp only [hermC_smul_left, hermC_sum_right, hermC_smul_right, Complex.conj_conj,
        dotProduct, Matrix.mulVec, Matrix.neg_apply, hSw, Pi.star_apply, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.star_def]
      ring
    have hWc : ∀ b, hermC τ.1 X.Gm W (X.colP x τ b) = 0 := by
      intro b
      rw [hWdef, hermC_sum_left]
      exact Finset.sum_eq_zero fun j _ => by rw [hermC_smul_left, hwc j b, mul_zero]
    have hW0 : W ≠ 0 := by
      intro hW
      let coef : Fin X.p0 ⊕ Fin k → ℂ :=
        Sum.elim (fun a => ∑ j, conj (xv j) * -α j a) (fun j => conj (xv j))
      have hsum : ∑ s, coef s • FD.col (mat x τ) (Sum.elim (Fin.castLE X.p0_le) gr s) = W := by
        rw [Fintype.sum_sum_type, hWdef]
        simp only [coef, Sum.elim_inl, Sum.elim_inr, wv, d, smul_add, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [add_comm, Finset.sum_comm]
        rfl
      have h0 : ∑ s, coef s • ((fun m => FD.col (mat x τ) m) ∘ Sum.elim (Fin.castLE X.p0_le) gr) s
          = 0 := hsum.trans hW
      have hcoef := Fintype.linearIndependent_iff.1 hli coef h0
      apply hxv
      funext j
      have := hcoef (Sum.inr j)
      simpa [coef] using this
    have hneg := neg_of_perp' X τ hA hW0 hWc
    have him : (hermC τ.1 X.Gm W W).im = 0 :=
      Complex.conj_eq_iff_im.1 (hermC_conj τ.1 hG W W)
    rw [hq, Complex.lt_def]
    constructor
    · simp only [Complex.zero_re, Complex.neg_re]
      linarith
    · simp [him]
  have hSpos : 0 < (-(D - α * B)).det := Matrix.PosDef.det_pos hS
  have hdetS : (D - α * B).det = (-1) ^ k * (-(D - α * B)).det := by
    rw [Matrix.det_neg, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    norm_num
  rw [hdetS, hik, OrthonormalChartBounds.psgn_add]
  have hz : A.det * ((-1) ^ k * (-(D - α * B)).det) =
      (((-1 : ℝ) ^ k : ℝ) : ℂ) * (A.det * (-(D - α * B)).det) := by
    push_cast
    ring
  have hre : 0 < (A.det * (-(D - α * B)).det).re := by
    have := (Complex.lt_def.1 (mul_pos hApos hSpos)).1
    simpa using this
  have h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hz, Complex.re_ofReal_mul, ← mul_assoc, h1, one_mul]
  exact hre

theorem psgn_dmin_le {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) (i : Fin (r + 1))
    (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  rw [psgn_eq_one hip, one_mul]
  have hsub : ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).PosDef :=
    hA.submatrix (Fin.castLE_injective hip)
  have heq : dmin X.Gm x τ i =
      ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).det := by
    unfold dmin lminor Data.gramPos
    rw [Matrix.submatrix_submatrix]
    rfl
  rw [heq]
  exact OrthonormalChartBounds.pos_re_of_posDef hsub

theorem mem_dom_of_gramPos {x : Frame X.Ψ r}
    (h : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ (X.gramPos x τ).PosDef) : x ∈ X.dom := by
  rw [Data.mem_dom_iff]
  intro τ
  refine ⟨(h τ).1, fun i => ?_⟩
  have hir := i.isLt
  by_cases hip : (i : ℕ) ≤ X.p0
  · exact psgn_dmin_le X τ (h τ).2 i hip
  · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = X.p0 + k := ⟨(i : ℕ) - X.p0, by omega⟩
    exact psgn_dmin_gt X τ (h τ).1 (h τ).2 k (by omega) i hk

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
