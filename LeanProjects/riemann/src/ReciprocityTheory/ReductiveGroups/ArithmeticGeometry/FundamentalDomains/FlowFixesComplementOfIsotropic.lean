import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

section onetau

variable (ξ : Fin r → E) (τ : X.Ψ)

private theorem flowMat_mulVec' (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v - (I * X.c τ * s * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  ext a
  simp only [Matrix.mulVec, dotProduct, flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hermC_sub_const_smul_left (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (v e w : Fin r → ℂ) (k : ℂ) :
    hermC σ G (v - k • e) w = hermC σ G v w - k * hermC σ G e w := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hermC_sub_const_smul_right (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (w v e : Fin r → ℂ) (k : ℂ) :
    hermC σ G w (v - k • e) = hermC σ G w v - conj k * hermC σ G w e := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  ring

lemma hC_flow_e (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) (s : ℂ) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ s) v) (emb τ.1 ξ) = hermC τ.1 X.Gm v (emb τ.1 ξ) := by
  rw [flowMat_mulVec', hermC_sub_const_smul_left, hiso, mul_zero, sub_zero]

lemma flow_fix (s : ℂ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (emb τ.1 ξ) = 0) :
    Matrix.mulVec (X.flowMat ξ τ s) v = v := by
  rw [flowMat_mulVec', hv, mul_zero, zero_smul, sub_zero]

lemma hC_right_flow (s : ℂ) (y v : Fin r → ℂ) (hy : hermC τ.1 X.Gm y (emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm y (Matrix.mulVec (X.flowMat ξ τ s) v) = hermC τ.1 X.Gm y v := by
  rw [flowMat_mulVec', hermC_sub_const_smul_right, hy, mul_zero, sub_zero]

lemma col_flow (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (a : Fin r) :
    col (mat (X.flow ξ s x) τ) a = Matrix.mulVec (X.flowMat ξ τ (s τ)) (col (mat x τ) a) := by
  ext k
  rfl

lemma mulVec_lin (M : Matrix (Fin r) (Fin r) ℂ) {n : ℕ} (β : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    Matrix.mulVec M (∑ a, β a • v a) = ∑ a, β a • Matrix.mulVec M (v a) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma ppos_flow {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom)
    (u : Fin r → ℂ) (hu : hermC τ.1 X.Gm u (emb τ.1 ξ) = 0)
    (hp : hermC τ.1 X.Gm (X.ppos x τ u) (emb τ.1 ξ) = 0) :
    X.ppos (X.flow ξ s x) τ u = X.ppos x τ u := by
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a with hα
  have hpx : X.ppos x τ u = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hT : ∑ a, α a • col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a) = X.ppos x τ u := by
    simp only [col_flow]
    rw [← mulVec_lin, ← hpx, flow_fix X ξ τ _ _ hp]
  rw [← hT]
  apply ppos_eq_of X (X.flow ξ s x) τ (gramPos_det_ne X hxs τ) u α
  intro b
  rw [hT, col_flow, hC_right_flow]
  · exact ppos_orth X x τ (gramPos_det_ne X hx τ) u b
  · rw [hC_sub_left, hu, hp, sub_zero]

private theorem hermC_sum_const_smul_left {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (cf : Fin n → ℂ) (w : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    hermC σ G (∑ a, cf a • w a) e = ∑ a, cf a * hermC σ G (w a) e := by
  have hadd : ∀ u u' : Fin r → ℂ, hermC σ G (u + u') e = hermC σ G u e + hermC σ G u' e := by
    intro u u'
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsm : ∀ (k : ℂ) (u : Fin r → ℂ), hermC σ G (k • u) e = k * hermC σ G u e := by
    intro k u
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have h0 : hermC σ G 0 e = 0 := by simp [hermC]
  suffices H : ∀ s : Finset (Fin n),
      hermC σ G (∑ a ∈ s, cf a • w a) e = ∑ a ∈ s, cf a * hermC σ G (w a) e from H _
  intro s
  refine Finset.induction_on s ?_ ?_
  · simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsm, ih]

lemma hC_ppos_e (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ v) (emb τ.1 ξ) =
      dotProduct (fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))
        (Matrix.mulVec (X.gramPos x τ)⁻¹
          (fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (emb τ.1 ξ))) := by
  unfold Data.ppos
  rw [hermC_sum_const_smul_left]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

lemma Hf_scale (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.Hf x τ v (emb τ.1 ξ) = k * X.Hf (X.flow ξ s x) τ v (emb τ.1 ξ) := by
  set e := emb τ.1 ξ with he
  set T := X.flowMat ξ τ (s τ) with hTdef
  set β : ℂ := -(I * X.c τ * s τ) with hβ
  set A := X.gramPos x τ with hAdef
  set A' := X.gramPos (X.flow ξ s x) τ with hA'def
  set l : Fin X.p0 → ℂ := fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) e with hl
  have hAdet := gramPos_det_ne X hx τ
  have hA'det := gramPos_det_ne X hxs τ
  have hsymm : ∀ v w, hermC τ.1 X.Gm v w = conj (hermC τ.1 X.Gm w v) := fun v w =>
    hC_symm τ.1 X.Gm X.Gm_herm w v

  have hA' : ∀ a b, A' a b = A a b + (β + conj β) * l a * conj (l b) := by
    intro a b
    have h1 : A' a b = hermC τ.1 X.Gm (Matrix.mulVec T (col (mat x τ) (Fin.castLE X.p0_le a)))
        (Matrix.mulVec T (col (mat x τ) (Fin.castLE X.p0_le b))) := by
      simp only [hA'def, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, col_flow, hTdef]
    rw [h1, flowMat_mulVec, flowMat_mulVec, hC_add_left, hC_add_right, hC_add_right, hC_smul_left,
      hC_smul_left, hC_smul_right, hC_smul_right, hiso, hsymm e (col (mat x τ) (Fin.castLE X.p0_le b))]
    simp only [hAdef, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hl, hβ, map_mul]
    ring

  have hA'mul : ∀ y : Fin X.p0 → ℂ, Matrix.mulVec A' y =
      Matrix.mulVec A y + ((β + conj β) * dotProduct (fun b => conj (l b)) y) • l := by
    intro y
    funext a
    simp only [Matrix.mulVec, dotProduct, hA', Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  set y := Matrix.mulVec A⁻¹ l with hy
  have hAy : Matrix.mulVec A y = l := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hAdet), Matrix.one_mulVec]
  set k : ℂ := 1 + (β + conj β) * dotProduct (fun b => conj (l b)) y with hk
  have hA'y : Matrix.mulVec A' y = k • l := by
    rw [hA'mul, hAy, hk, add_smul, one_smul]
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hA'y
    have hy0 : y = 0 := by
      have := congrArg (Matrix.mulVec A'⁻¹) hA'y
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA'det), Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    have hl0 : l = 0 := by rw [← hAy, hy0, Matrix.mulVec_zero]
    rw [hk] at h0
    simp [hy0] at h0
  have hyk : y = k • Matrix.mulVec A'⁻¹ l := by
    have := congrArg (Matrix.mulVec A'⁻¹) hA'y
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA'det), Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
  refine ⟨k, hk0, fun v hv => ?_⟩
  have hcv : (fun b => hermC τ.1 X.Gm v (col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le b))) =
      fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) := by
    funext b; rw [col_flow, hC_right_flow X ξ τ _ _ _ hv]
  have hlT : (fun a => hermC τ.1 X.Gm (col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a)) e) = l := by
    funext a; rw [col_flow, hC_flow_e X ξ τ hiso]
  simp only [Hf]
  rw [hC_sub_left, hC_sub_left, hC_smul_left, hC_smul_left, hv, sub_zero, sub_zero,
    hC_ppos_e, hC_ppos_e, hcv, hlT]
  rw [show Matrix.mulVec (X.gramPos x τ)⁻¹ (fun a => hermC τ.1 X.Gm (col (mat x τ)
      (Fin.castLE X.p0_le a)) e) = y from rfl, hyk, dotProduct_smul, smul_eq_mul]
  ring

end onetau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
