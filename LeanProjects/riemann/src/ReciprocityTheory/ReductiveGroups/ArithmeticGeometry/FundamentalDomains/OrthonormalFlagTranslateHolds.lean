import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace FrameDegreeData

noncomputable section

variable {r : ℕ} (X : Data E r)

lemma upper_of_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) : (mat b τ).BlockTriangular id := by
  intro i j hij
  exact (hb τ).2 i j hij

lemma bdiag_ne {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (j : Fin r) : b τ j j ≠ 0 := by
  have h1 := (hb τ).1
  rw [Matrix.det_of_upperTriangular (upper_of_bor X hb τ)] at h1
  exact (Finset.prod_ne_zero_iff.1 h1) j (Finset.mem_univ _)

private theorem sum_eq_sum_castLE_of_eq_zero {n m : ℕ} (h : m ≤ n) (f : Fin n → ℂ)
    (hf : ∀ j : Fin n, m ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j : Fin m, f (Fin.castLE h j) := by
  refine Eq.trans ?_ (Finset.sum_map (Finset.univ : Finset (Fin m)) ⟨Fin.castLE h, Fin.castLE_injective h⟩ f)
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  push_neg at hlt
  exact hj (Finset.mem_map.2 ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

private theorem gram_eq_lemma {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a c
  simp only [gram, Matrix.of_apply, hermC, col, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma dmin_rmul (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (rmul x b) τ i =
      (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        dmin X.Gm x τ i *
        conj (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have hB := upper_of_bor X hb τ
  have hmat : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  unfold dmin lminor
  rw [hmat, gram_eq_lemma, gram_eq_lemma τ.1 X.Gm (mat x τ), Matrix.transpose_mul, Matrix.map_mul]
  have hre : (mat b τ)ᵀ * (mat x τ)ᵀ * X.Gm.map τ.1 *
      ((mat x τ).map (starRingEnd ℂ) * (mat b τ).map (starRingEnd ℂ)) =
      (mat b τ)ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        (mat b τ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc]
  rw [hre]
  set A := (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) with hA
  set B := mat b τ with hBdef
  set e : Fin i → Fin r := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  have hlt : ∀ (a : Fin i) (j : Fin r), (i : ℕ) ≤ j.val → e a < j := by
    intro a j hj
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE]
    have := a.isLt
    omega
  have hsub : (Bᵀ * A * B.map (starRingEnd ℂ)).submatrix e e =
      (B.submatrix e e)ᵀ * A.submatrix e e * (B.submatrix e e).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [sum_eq_sum_castLE_of_eq_zero (Nat.le_of_lt_succ i.isLt) _ (fun k hk => by
      have h0 : B k (e c) = 0 := hB (hlt c k hk)
      rw [h0, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact sum_eq_sum_castLE_of_eq_zero (Nat.le_of_lt_succ i.isLt) _ (fun j hj => by
      have h0 : B j (e a) = 0 := hB (hlt a j hj)
      rw [h0, zero_mul])
  have hBe : (B.submatrix e e).BlockTriangular id := by
    intro j k hjk
    apply hB
    show e k < e j
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE, Fin.coe_castLE]
    exact hjk
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show ((B.submatrix e e).map (starRingEnd ℂ)).det = starRingEnd ℂ (B.submatrix e e).det from
      (RingHom.map_det _ _).symm,
    Matrix.det_of_upperTriangular hBe]
  rfl

lemma ratio_rmul (x : Frame X.Ψ r) (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (k : Fin r) :
    ‖dmin X.Gm (rmul x b) τ k.succ / dmin X.Gm (rmul x b) τ k.castSucc‖ =
      ‖b τ k k‖ ^ 2 * ‖dmin X.Gm x τ k.succ / dmin X.Gm x τ k.castSucc‖ := by
  have hsucc : (∏ j : Fin (k.succ : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)) =
      (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)) * b τ k k := by
    change (∏ j : Fin ((k : ℕ) + 1), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)) = _
    rw [Fin.prod_univ_castSucc]
    rfl
  have hPk : (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => bdiag_ne X hb τ _
  rw [dmin_rmul X x hb τ k.succ, dmin_rmul X x hb τ k.castSucc, hsucc]
  set Pk := (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j))
  have hPn : ‖Pk‖ ≠ 0 := norm_ne_zero_iff.2 hPk
  simp only [norm_div, norm_mul, map_mul, Complex.norm_conj]
  by_cases hd : ‖dmin X.Gm x τ k.castSucc‖ = 0
  · simp [hd]
  · field_simp

lemma factor_eq (t q : ℝ) (ht : 0 < t) (hq : 0 ≤ q) (l : ℤ) :
    t ^ l * (t ^ 2 * q) ^ (-(l : ℝ) / 2) = q ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) hq]
  have h1 : (t ^ 2) ^ (-(l : ℝ) / 2) = (t ^ l)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_intCast]
  rw [h1, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht.ne'), one_mul]

lemma pnorm_rmul (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) : X.pnorm la P (rmul x b) = X.pnorm la P x := by
  have hfac : ∀ (τ : X.Ψ) (i : Fin r), ‖b τ i i‖ ^ la τ i *
      (‖b τ i i‖ ^ 2 * ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖) ^ (-(la τ i : ℝ) / 2) =
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
    fun τ i => factor_eq _ _ (norm_pos_iff.2 (bdiag_ne X hb τ i)) (norm_nonneg _) _
  unfold Data.pnorm
  rw [hP x hx b hb, norm_mul]
  simp only [ratio_rmul X x hx hb]
  unfold bchar
  simp only [norm_prod, norm_zpow]
  rw [← Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => hfac τ i]
  simp only [Finset.prod_mul_distrib]
  ring

private theorem hermC_sub_left_of_natDim {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u v w : Fin r → ℂ) : hermC τ G (u - v) w = hermC τ G u w - hermC τ G v w := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hermC_eq_zero_of_mem_span' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (w : Fin r → ℂ)
    (S : Set (Fin r → ℂ)) (h : ∀ s ∈ S, hermC τ G w s = 0) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ S) : hermC τ G w v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [hermC]
  | add x y _ _ hx hy =>
    have e : hermC τ G w (x + y) = hermC τ G w x + hermC τ G w y := by
      simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    rw [e, hx, hy, add_zero]
  | smul c x _ hx =>
    have e : hermC τ G w (c • x) = (starRingEnd ℂ) c * hermC τ G w x := by
      simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e, hx, mul_zero]

lemma ppos_sameFlag {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (h : X.SameFlag x x')
    (τ : X.Ψ) (u : Fin r → ℂ) : X.ppos x τ u = X.ppos x' τ u := by
  have hspan := h τ
  have hmem : ∀ y : Frame X.Ψ r, X.ppos y τ u ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)) := by
    intro y
    rw [X.ppos_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have horth : ∀ y ∈ X.dom, ∀ c ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)),
      hermC τ.1 X.Gm (X.ppos y τ u - u) c = 0 := by
    intro y hy c hc
    refine hermC_eq_zero_of_mem_span' τ.1 X.Gm _ _ (fun s hs => ?_) hc
    obtain ⟨d, rfl⟩ := hs
    rw [hermC_sub_left_of_natDim]
    exact sub_eq_zero.2 (X.hermC_ppos_colP hy τ u d)
  set v := X.ppos x τ u - X.ppos x' τ u with hv
  have hvmem : v ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) := by
    refine Submodule.sub_mem _ (hmem x) ?_
    rw [hspan]
    exact hmem x'
  have hvperp : ∀ c ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)),
      hermC τ.1 X.Gm v c = 0 := by
    intro c hc
    have e : v = (X.ppos x τ u - u) - (X.ppos x' τ u - u) := by
      rw [hv]
      abel
    rw [e, hermC_sub_left_of_natDim, horth x hx c hc, horth x' hx' c (hspan ▸ hc), sub_zero]
  by_contra hne
  have hne' : v ≠ 0 := sub_ne_zero.2 hne
  have hlt := X.neg_of_perp hx τ hne' (fun b => hvperp _ (Submodule.subset_span ⟨b, rfl⟩))
  rw [hvperp v hvmem] at hlt
  simp at hlt

lemma Hf_sameFlag {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (h : X.SameFlag x x') :
    X.Hf x = X.Hf x' := by
  funext τ u w
  simp only [Data.Hf, ppos_sameFlag X hx hx' h τ u]

end

end FrameDegreeData

theorem orthonormalFlagTranslate_holds : OrthonormalFlagTranslate (E := E) := by
  intro r X
  refine ⟨fun x hx => ⟨FrameDegreeData.bOf X x, FrameDegreeData.bOf_mem X hx, FrameDegreeData.ortho_bOf X hx⟩,
    fun la P hP x hx b hb => FrameDegreeData.pnorm_rmul X la P hP x hx b hb, fun x hx x' hx' h => ?_⟩
  have hpp := FrameDegreeData.ppos_sameFlag X hx hx' h
  have hJ : X.Jz x = X.Jz x' := by
    funext u τ
    simp only [Data.Jz, hpp]
  refine ⟨fun ξ => ⟨hJ, ?_, ?_⟩, ?_⟩
  · simp only [Data.Uz, hJ]
  · unfold Data.aproj
    rw [FrameDegreeData.Hf_sameFlag X hx hx' h]
  · funext τ v
    have e : ∀ y : Frame X.Ψ r, X.posPart y τ v = (hermC τ.1 X.Gm (X.ppos y τ v) v).re := by
      intro y
      rw [X.hermC_ppos_self]
      rfl
    simp only [Data.maj, e, hpp]

end ReciprocityTheory.ChartRestriction.G.FD
