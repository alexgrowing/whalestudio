import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace MajorantNormalForms

open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem col_mul_eq (P B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (P * B) a = ∑ k, B k a • col P k := by
  funext i
  simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def jpL (x : Frame X.Ψ r) (τ : X.Ψ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := X.jp x τ
  map_add' := X.jp_add x τ
  map_smul' := X.jp_smul x τ

noncomputable def pposL (x : Frame X.Ψ r) (τ : X.Ψ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := X.ppos x τ
  map_add' := X.ppos_add x τ
  map_smul' := X.ppos_smul_eq x τ

theorem ppos_sum (x : Frame X.Ψ r) (τ : X.Ψ) (c : Fin r → ℂ) (u : Fin r → Fin r → ℂ) :
    X.ppos x τ (∑ a, c a • u a) = ∑ a, c a • X.ppos x τ (u a) := by
  have h := map_sum (pposL X x τ) (fun a => c a • u a) Finset.univ
  simp only [map_smul] at h
  exact h

private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC τ G (∑ k, u k • v k) y = ∑ k, u k * hermC τ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC τ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC τ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC τ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC τ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h

theorem Hf_sum_sum (x : Frame X.Ψ r) (τ : X.Ψ) (c d : Fin r → ℂ) (u w : Fin r → Fin r → ℂ) :
    X.Hf x τ (∑ a, c a • u a) (∑ b, d b • w b) =
      ∑ a, ∑ b, c a * conj (d b) * X.Hf x τ (u a) (w b) := by
  have hz : (2 : ℂ) • X.ppos x τ (∑ a, c a • u a) - ∑ a, c a • u a =
      ∑ a, c a • ((2 : ℂ) • X.ppos x τ (u a) - u a) := by
    rw [ppos_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_sub, smul_comm]
  unfold Data.Hf
  rw [hz, hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem ppos_colP {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.ppos x τ (X.colP x τ d) = X.colP x τ d := by
  have hdet : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have h1 : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
    rw [h1, Complex.zero_re, mul_zero] at h
    exact lt_irrefl _ h
  unfold Data.ppos Data.colP
  have hG : ∀ a b : Fin X.p0, hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = X.gramPos x τ a b := fun a b => rfl
  simp only [hG]
  have hmul : ∀ a, ∑ b, X.gramPos x τ d b * (X.gramPos x τ)⁻¹ b a = if d = a then 1 else 0 := by
    intro a
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_apply]
  simp only [hmul, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) =
      (X.gramPos x τ)⁻¹ by rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma maj_eq_lemma_4 (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = (X.Hf x τ v v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.Hf
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp

private lemma hermC_smul_sub_right_lemma_6 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma Hf_conj_lemma_7 (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  unfold Data.Hf
  rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_6, hermC_smul_sub_left_lemma_3,
    hermC_ppos_lemma_5 X x τ w u, map_ofNat]

theorem hgram_posDef {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    (Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext a c
    show star (X.Hf x τ (col (mat x τ) c) (col (mat x τ) a)) =
      X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)
    rw [Complex.star_def, Hf_conj_lemma_7]
  have hy : star v ⬝ᵥ ((Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)) *ᵥ v) =
      X.Hf x τ (∑ a, star (v a) • col (mat x τ) a) (∑ a, star (v a) • col (mat x τ) a) := by
    rw [Hf_sum_sum]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      Complex.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hy0 : (∑ a, star (v a) • col (mat x τ) a) ≠ 0 := by
    intro h0
    have hmv : mat x τ *ᵥ (fun a => star (v a)) = ∑ a, star (v a) • col (mat x τ) a := by
      funext i
      show ∑ k, mat x τ i k * star (v k) = (∑ a, star (v a) • col (mat x τ) a) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [← hmv] at h0
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (hx τ).1 h0
    apply hv
    funext a
    have h2 := congrFun h1 a
    simpa using h2
  have hpos := X.maj_pos hx τ hy0
  rw [maj_eq_lemma_4 X x τ] at hpos
  have him := Complex.conj_eq_iff_im.mp (Hf_conj_lemma_7 X x τ (∑ a, star (v a) • col (mat x τ) a)
    (∑ a, star (v a) • col (mat x τ) a))
  rw [hy]
  exact Complex.lt_def.mpr ⟨hpos, him.symm⟩

theorem exists_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, B.det ≠ 0 ∧ (∀ a c : Fin r, c < a → B a c = 0) ∧
      ∀ a c : Fin r, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) =
        if a = c then 1 else 0 := by
  have hH := hgram_posDef X hx τ
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ,
      H = Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c) := ⟨_, rfl⟩
  rw [← hHd] at hH
  have hD := LDL.diag_eq_lowerInv_conj hH
  have hLdet : (LDL.lowerInv hH).det ≠ 0 := (Matrix.isUnit_det_of_invertible _).ne_zero
  obtain ⟨D, hDd⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ,
      D = LDL.lowerInv hH * H * (LDL.lowerInv hH)ᴴ := ⟨_, rfl⟩
  have hDoff : ∀ a c, a ≠ c → D a c = 0 := by
    intro a c hac
    rw [hDd, ← hD]
    exact Matrix.diagonal_apply_ne _ hac
  have hdpos : ∀ i : Fin r, 0 < (D i i).re ∧ (D i i).im = 0 := by
    intro i
    have hx0 : star (LDL.lowerInv hH i) ≠ 0 := by
      intro h0
      apply hLdet
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      have h1 := congrFun h0 j
      simpa using h1
    have hp := hH.dotProduct_mulVec_pos hx0
    have he : D i i = star (star (LDL.lowerInv hH i)) ⬝ᵥ (H *ᵥ star (LDL.lowerInv hH i)) := by
      rw [hDd]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
        star_star, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [he]
    exact ⟨(Complex.lt_def.mp hp).1, (Complex.lt_def.mp hp).2.symm⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin r → ℝ, s = fun c => (Real.sqrt (D c c).re)⁻¹ := ⟨_, rfl⟩
  have hs0 : ∀ c, s c ≠ 0 := fun c => by
    rw [hs]
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (hdpos c).1)
  refine ⟨(LDL.lowerInv hH)ᵀ * diagonal (fun c => (s c : ℂ)), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero hLdet (Finset.prod_ne_zero_iff.mpr fun c _ =>
      Complex.ofReal_ne_zero.mpr (hs0 c))
  · intro a c hca
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, LDL.lowerInv_triangular hH hca, zero_mul]
  · intro a c
    rw [col_mul_eq, col_mul_eq, Hf_sum_sum]
    have hHkl : ∀ k l, X.Hf x τ (col (mat x τ) k) (col (mat x τ) l) = H k l := fun k l => by
      rw [hHd]
      rfl
    simp only [hHkl, Matrix.mul_diagonal, Matrix.transpose_apply]
    calc _ = (s a : ℂ) * (s c : ℂ) * D a c := by
          rw [hDd]
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, map_mul,
            Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      _ = if a = c then 1 else 0 := by
          by_cases hac : a = c
          · subst hac
            rw [if_pos rfl]
            have hr := (hdpos a).1
            have hre : D a a = ((D a a).re : ℂ) := Complex.ext rfl (by simp [(hdpos a).2])
            have hsq : Real.sqrt (D a a).re * Real.sqrt (D a a).re = (D a a).re :=
              Real.mul_self_sqrt hr.le
            have hne : Real.sqrt (D a a).re ≠ 0 := Real.sqrt_ne_zero'.mpr hr
            have h1 : s a * s a * (D a a).re = 1 := by
              rw [hs, ← hsq]
              field_simp
            rw [hre]
            exact_mod_cast h1
          · rw [if_neg hac, hDoff a c hac, mul_zero]

theorem Hf_eq_of_pos (x : Frame X.Ψ r) (τ : X.Ψ) {u : Fin r → ℂ} (hu : X.ppos x τ u = u)
    (w : Fin r → ℂ) : X.Hf x τ u w = hermC τ.1 X.Gm u w := by
  unfold Data.Hf
  rw [hu, two_smul, add_sub_cancel_right]

theorem Hf_eq_of_zero (x : Frame X.Ψ r) (τ : X.Ψ) {u : Fin r → ℂ} (hu : X.ppos x τ u = 0)
    (w : Fin r → ℂ) : X.Hf x τ u w = -hermC τ.1 X.Gm u w := by
  unfold Data.Hf
  rw [hu, smul_zero, zero_sub]
  simp only [hermC, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem gram_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {B : Matrix (Fin r) (Fin r) ℂ}
    (hBd : B.det ≠ 0) (hBt : ∀ a c : Fin r, c < a → B a c = 0)
    (hB : ∀ a c, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) = if a = c then 1 else 0) :
    gram τ.1 X.Gm (mat x τ * B) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  have hpos : ∀ a : Fin r, (a : ℕ) < X.p0 →
      X.ppos x τ (col (mat x τ * B) a) = col (mat x τ * B) a := by
    intro a ha
    rw [col_mul_eq, ppos_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0
    · have h := ppos_colP X hx τ ⟨k, hk⟩
      simp only [Data.colP] at h
      rw [show Fin.castLE X.p0_le ⟨(k : ℕ), hk⟩ = k from Fin.ext rfl] at h
      rw [h]
    · rw [hBt k a (Fin.lt_iff_val_lt_val.mpr (by omega))]
      simp
  have hzero : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → X.ppos x τ (col (mat x τ * B) a) = 0 := by
    intro a ha
    have h1 : ∀ j : Fin r, (j : ℕ) < X.p0 →
        hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) j) = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => by
        subst h
        omega
      have h := hB a j
      rw [if_neg hne] at h
      unfold Data.Hf at h
      rw [hermC_smul_sub_left_lemma_3, hermC_ppos_lemma_5 X x τ, hpos j hj] at h
      linear_combination h
    have hBinv : ∀ i j : Fin r, j < i → B⁻¹ i j = 0 := by
      haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hBd)
      intro i j hij
      exact Matrix.blockTriangular_inv_of_blockTriangular (b := id)
        (fun i' j' h' => hBt i' j' h' : B.BlockTriangular id) hij
    have hc : ∀ k, col (mat x τ) k = ∑ j, B⁻¹ j k • col (mat x τ * B) j := by
      intro k
      have hY : mat x τ = (mat x τ * B) * B⁻¹ := by
        rw [mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hBd), mul_one]
      conv_lhs => rw [hY]
      exact col_mul_eq (mat x τ * B) B⁻¹ k
    have h2 : ∀ b : Fin X.p0,
        hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
      intro b
      rw [hc, hermC_sum_right_lemma_2]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < X.p0
      · rw [h1 j hj, mul_zero]
      · rw [hBinv j (Fin.castLE X.p0_le b)
          (Fin.lt_iff_val_lt_val.mpr (by simp only [Fin.coe_castLE]; omega)), map_zero, zero_mul]
    unfold Data.ppos
    simp only [h2, zero_mul, Finset.sum_const_zero, zero_smul]
  ext a c
  show hermC τ.1 X.Gm (col (mat x τ * B) a) (col (mat x τ * B) c) = diagonal _ a c
  rw [Matrix.diagonal_apply]
  have hBac := hB a c
  by_cases ha : (a : ℕ) < X.p0
  · rw [Hf_eq_of_pos X x τ (hpos a ha)] at hBac
    rw [hBac]
    simp only [sgn, if_pos ha, Complex.ofReal_one]
  · rw [Hf_eq_of_zero X x τ (hzero a (not_lt.mp ha))] at hBac
    rw [neg_eq_iff_eq_neg.mp hBac]
    simp only [sgn, if_neg ha, Complex.ofReal_neg, Complex.ofReal_one]
    split_ifs <;> simp

theorem maj_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {B : Matrix (Fin r) (Fin r) ℂ}
    (hBd : B.det ≠ 0)
    (hB : ∀ a c, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) = if a = c then 1 else 0)
    (v : Fin r → ℂ) : X.maj x τ v = ∑ a, ‖((mat x τ * B)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hdetY : (mat x τ * B).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hBd
  have hv : v = ∑ a, ((mat x τ * B)⁻¹ *ᵥ v) a • col (mat x τ * B) a := by
    have h1 : (mat x τ * B) *ᵥ ((mat x τ * B)⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY),
        Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext i
    show ∑ k, (mat x τ * B) i k * ((mat x τ * B)⁻¹ *ᵥ v) k =
      (∑ a, ((mat x τ * B)⁻¹ *ᵥ v) a • col (mat x τ * B) a) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [maj_eq_lemma_4 X x τ v]
  conv_lhs => rw [hv]
  rw [Hf_sum_sum]
  simp only [hB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem exists_normal_frame {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, ∀ τ : X.Ψ,
      gram τ.1 X.Gm (mat (rmul x b) τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
      ∀ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  choose B hBd hBt hB using fun τ => exists_normal X hx τ
  refine ⟨fun τ => B τ, fun τ => ⟨hBd τ, hBt τ⟩, fun τ => ⟨?_, fun v => ?_⟩⟩
  · exact gram_normal X hx τ (hBd τ) (hBt τ) (hB τ)
  · exact maj_normal X hx τ (hBd τ) (hB τ) v

end MajorantNormalForms

end ReciprocityTheory.ChartRestriction.G.FD
