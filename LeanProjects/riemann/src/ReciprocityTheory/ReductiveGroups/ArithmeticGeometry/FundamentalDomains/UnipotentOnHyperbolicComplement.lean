import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable section

section herm

variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

private lemma hermC_sub_left_section (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hermC_add_right_section (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma hermC_smul_right_section (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_sub_right (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma hC_zero_left (v : Fin r → ℂ) : hermC τ G 0 v = 0 := by
  simp [hermC]

def hL (y : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hermC τ G v y
  map_add' u v := hC_add_left τ G u v y
  map_smul' c v := by
    simp only [smul_eq_mul, RingHom.id_apply]
    exact hC_smul_left τ G c v y

def rz (φ : (Fin r → ℂ) →ₗ[ℂ] ℂ) : Fin r → ℂ :=
  fun b => conj (((G.map τ)⁻¹).mulVec (fun a => φ (fun j => if a = j then 1 else 0)) b)

lemma rz_spec (hG : (G.map τ).det ≠ 0) (φ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (v : Fin r → ℂ) :
    hermC τ G v (rz τ G φ) = φ v := by
  have hM : G.map τ * (G.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)
  have key : ∀ a, ∑ b, τ (G a b) * (((G.map τ)⁻¹).mulVec
      (fun a => φ (fun j => if a = j then 1 else 0))) b = φ (fun j => if a = j then 1 else 0) := by
    intro a
    have h2 := congrFun (Matrix.mulVec_mulVec (fun a => φ (fun j => if a = j then 1 else 0))
      (G.map τ) (G.map τ)⁻¹) a
    rw [hM, Matrix.one_mulVec] at h2
    simpa [Matrix.mulVec, dotProduct] using h2
  have hv : v = ∑ a, v a • (fun j => if a = j then (1 : ℂ) else 0) := by
    funext j
    simp [Finset.sum_apply]
  calc hermC τ G v (rz τ G φ)
      = ∑ a, v a * ∑ b, τ (G a b) * (((G.map τ)⁻¹).mulVec
          (fun a => φ (fun j => if a = j then 1 else 0))) b := by
        simp only [hermC, rz, Complex.conj_conj, Finset.mul_sum, mul_assoc]
    _ = ∑ a, v a * φ (fun j => if a = j then 1 else 0) := by simp only [key]
    _ = φ v := by
        conv_rhs => rw [hv]
        simp only [map_sum, map_smul, smul_eq_mul]

lemma map_det_ne (hG : G.det ≠ 0) : (G.map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).mpr hG

end herm

namespace Data

variable {r : ℕ} (X : Data E r)

lemma positive_part_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u + v) = X.ppos x τ u + X.ppos x τ v := by
  simp only [ppos, hC_add_left, add_mul, Finset.sum_add_distrib, add_smul]

private lemma hermC_Gm_eq_conj_swap (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm u w = conj (hermC τ.1 X.Gm w u) := by
  have hG : ∀ a b, τ.1 (X.Gm a b) = conj (τ.1 (X.Gm b a)) := fun a b => by
    rw [← X.Gm_herm b a, cc]
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _ _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _ _).symm
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG a b]
  ring

private lemma hermC_finset_sum_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) w = ∑ i ∈ s, hermC τ G (f i) w := by
  induction s using Finset.cons_induction with
  | empty => simp [hC_zero_left]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hC_add_left, ih]

private lemma hermC_finset_sum_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (f : ι → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hermC]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hermC_add_right_section, ih]

private lemma sum_mul_mul_eq_of_mul_eq_one {n : ℕ} (k : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : A * B = 1) (a : Fin n) : ∑ b, (∑ a', k a' * A a' b) * B b a = k a := by
  calc ∑ b, (∑ a', k a' * A a' b) * B b a = Matrix.vecMul (Matrix.vecMul k A) B a := rfl
    _ = Matrix.vecMul k (A * B) a := by rw [Matrix.vecMul_vecMul]
    _ = k a := by rw [h, Matrix.vecMul_one]

lemma ppos_idem {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ (X.ppos x τ v) = X.ppos x τ v := by
  have hdet : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have h1 : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
    rw [h1] at h
    simp at h
  have hinv : X.gramPos x τ * (X.gramPos x τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hP : ∀ b, hermC τ.1 X.Gm (X.ppos x τ v) (col (mat x τ) (Fin.castLE X.p0_le b)) =
      ∑ a', (∑ b', hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a') *
        X.gramPos x τ a' b := by
    intro b
    simp only [ppos, hermC_finset_sum_left, hC_smul_left]
    rfl
  show ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm (X.ppos x τ v) (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a) • col (mat x τ) (Fin.castLE X.p0_le a) = X.ppos x τ v
  simp only [hP]
  simp only [sum_mul_mul_eq_of_mul_eq_one (fun a' => ∑ b', hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a')
    _ _ hinv]
  rfl

def Jp (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ := (2 : ℂ) • X.ppos x τ v - v

lemma Jp_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u + v) = X.Jp x τ u + X.Jp x τ v := by
  funext i
  simp only [Jp, positive_part_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma ppos_smul' (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, Finset.mul_sum]

private lemma ppos_sub' (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  have h := X.positive_part_add x τ u ((-1 : ℂ) • v)
  rw [ppos_smul'] at h
  simpa [sub_eq_add_neg, neg_one_smul] using h

lemma Jp_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.Jp x τ (c • v) = c • X.Jp x τ v := by
  funext i
  simp only [Jp, ppos_smul', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma Jp_Jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.Jp x τ (X.Jp x τ v) = v := by
  simp only [Jp]
  rw [ppos_sub', ppos_smul', X.ppos_idem hx]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma hermC_ppos_left_eq_ppos_right_frame (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hH : (X.gramPos x τ).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply]
    exact (X.hermC_Gm_eq_conj_swap τ (col (mat x τ) (Fin.castLE X.p0_le a)) (col (mat x τ) (Fin.castLE X.p0_le b))).symm
  have hGi : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b :=
    fun a b => hH.inv.apply a b
  simp only [ppos, hermC_finset_sum_left, hermC_finset_sum_right, hC_smul_left, hermC_smul_right_section, map_sum,
    map_mul]
  simp only [← X.hermC_Gm_eq_conj_swap, hGi, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma Jp_adj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.Jp x τ u) w = hermC τ.1 X.Gm u (X.Jp x τ w) := by
  simp only [Jp, hermC_sub_left_section, hC_sub_right, hC_smul_left, hermC_smul_right_section, X.hermC_ppos_left_eq_ppos_right_frame,
    map_ofNat]

section perTau

variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)

def d2q : ℂ := X.Hf x τ e e

def d2b : (Fin r → ℂ) →ₗ[ℂ] ℂ := (X.d2q x τ e)⁻¹ • hL τ.1 X.Gm e

def d2a : (Fin r → ℂ) →ₗ[ℂ] ℂ := (X.d2q x τ e)⁻¹ • hL τ.1 X.Gm (X.Jp x τ e)

def d2pi : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.id - (X.d2a x τ e).smulRight e - (X.d2b x τ e).smulRight (X.Jp x τ e)

def d2z : Fin r → ℂ := rz τ.1 X.Gm ((X.d2q x τ e) • (δ ∘ₗ X.d2pi x τ e))

def d2nL : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.id + (δ ∘ₗ X.d2pi x τ e - (δ (X.d2z x τ e δ) / 2) • X.d2b x τ e).smulRight e -
    (X.d2b x τ e).smulRight (X.d2z x τ e δ)

def d2n : Matrix (Fin r) (Fin r) ℂ := LinearMap.toMatrix' (X.d2nL x τ e δ)

lemma hyperbolic_coeff_b_apply (v : Fin r → ℂ) :
    X.d2b x τ e v = (X.d2q x τ e)⁻¹ * hermC τ.1 X.Gm v e := rfl

lemma hyperbolic_coeff_a_apply (v : Fin r → ℂ) :
    X.d2a x τ e v = (X.d2q x τ e)⁻¹ * hermC τ.1 X.Gm v (X.Jp x τ e) := rfl

lemma hyperbolic_projection_apply (v : Fin r → ℂ) :
    X.d2pi x τ e v = v - X.d2a x τ e v • e - X.d2b x τ e v • X.Jp x τ e := rfl

lemma unipotent_mulVec_formula (v : Fin r → ℂ) :
    Matrix.mulVec (X.d2n x τ e δ) v = v + (δ (X.d2pi x τ e v) -
      δ (X.d2z x τ e δ) / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • X.d2z x τ e δ := by
  simp only [d2n, LinearMap.toMatrix'_mulVec]
  rfl

variable {x τ e}

lemma hsym (u w : Fin r → ℂ) : hermC τ.1 X.Gm u w = conj (hermC τ.1 X.Gm w u) := by
  have hG : ∀ a b, τ.1 (X.Gm a b) = conj (τ.1 (X.Gm b a)) := fun a b => by
    rw [← X.Gm_herm b a, cc]
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _ _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _ _).symm
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _).symm
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG a b]
  ring

lemma hermitian_pairing_Je_e : hermC τ.1 X.Gm (X.Jp x τ e) e = X.d2q x τ e := rfl

lemma hermitian_pairing_e_Je (hx : x ∈ X.dom) : hermC τ.1 X.Gm e (X.Jp x τ e) = X.d2q x τ e := (X.Jp_adj hx τ e e).symm.trans X.hermitian_pairing_Je_e

lemma hermitian_pairing_Je_Je_zero (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) :
    hermC τ.1 X.Gm (X.Jp x τ e) (X.Jp x τ e) = 0 := by
  rw [X.Jp_adj hx τ e (X.Jp x τ e), X.Jp_Jp hx τ e, he]

variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq

lemma hyperbolic_projection_e : X.d2pi x τ e e = 0 := by
  rw [hyperbolic_projection_apply, hyperbolic_coeff_a_apply, hyperbolic_coeff_b_apply, X.hermitian_pairing_e_Je hx, he, inv_mul_cancel₀ hq]
  simp

lemma hyperbolic_projection_Je : X.d2pi x τ e (X.Jp x τ e) = 0 := by
  rw [hyperbolic_projection_apply, hyperbolic_coeff_a_apply, hyperbolic_coeff_b_apply, X.hermitian_pairing_Je_Je_zero hx he, X.hermitian_pairing_Je_e, inv_mul_cancel₀ hq]
  simp

lemma hyperbolic_projection_of_perp {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0)
    (hu2 : hermC τ.1 X.Gm u (X.Jp x τ e) = 0) : X.d2pi x τ e u = u := by
  rw [hyperbolic_projection_apply, hyperbolic_coeff_a_apply, hyperbolic_coeff_b_apply, hu1, hu2]
  simp

lemma hyperbolic_projection_perp_e (v : Fin r → ℂ) : hermC τ.1 X.Gm (X.d2pi x τ e v) e = 0 := by
  rw [hyperbolic_projection_apply, hermC_sub_left_section, hermC_sub_left_section, hC_smul_left, hC_smul_left, he, X.hermitian_pairing_Je_e,
    hyperbolic_coeff_b_apply, mul_zero, sub_zero, inv_mul_eq_div, div_mul_cancel₀ _ hq, sub_self]

lemma hyperbolic_projection_perp_Je (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.d2pi x τ e v) (X.Jp x τ e) = 0 := by
  rw [hyperbolic_projection_apply, hermC_sub_left_section, hermC_sub_left_section, hC_smul_left, hC_smul_left, X.hermitian_pairing_e_Je hx,
    X.hermitian_pairing_Je_Je_zero hx he, hyperbolic_coeff_a_apply, mul_zero, sub_zero, inv_mul_eq_div, div_mul_cancel₀ _ hq, sub_self]

lemma unipotent_shift_spec (v : Fin r → ℂ) :
    hermC τ.1 X.Gm v (X.d2z x τ e δ) = X.d2q x τ e * δ (X.d2pi x τ e v) := by
  simp only [d2z]
  rw [rz_spec _ _ (map_det_ne _ _ X.Gm_det)]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]

lemma unipotent_shift_orthogonal_e : hermC τ.1 X.Gm (X.d2z x τ e δ) e = 0 := by
  rw [X.hsym, X.unipotent_shift_spec δ hx he hq, X.hyperbolic_projection_e hx he hq]
  simp

lemma unipotent_shift_orthogonal_Je : hermC τ.1 X.Gm (X.d2z x τ e δ) (X.Jp x τ e) = 0 := by
  rw [X.hsym, X.unipotent_shift_spec δ hx he hq, X.hyperbolic_projection_Je hx he hq]
  simp

lemma d2pi_d2z_eq_d2z : X.d2pi x τ e (X.d2z x τ e δ) = X.d2z x τ e δ := X.hyperbolic_projection_of_perp hx he hq (X.unipotent_shift_orthogonal_e δ hx he hq) (X.unipotent_shift_orthogonal_Je δ hx he hq)

lemma unipotent_shift_self_pairing : hermC τ.1 X.Gm (X.d2z x τ e δ) (X.d2z x τ e δ) =
    X.d2q x τ e * δ (X.d2z x τ e δ) := by
  rw [X.unipotent_shift_spec δ hx he hq, X.d2pi_d2z_eq_d2z δ hx he hq]

lemma unipotent_fixes_e : Matrix.mulVec (X.d2n x τ e δ) e = e := by
  rw [unipotent_mulVec_formula, X.hyperbolic_projection_e hx he hq, hyperbolic_coeff_b_apply, he]
  simp

lemma unipotent_on_orthogonal_e {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0) :
    Matrix.mulVec (X.d2n x τ e δ) u = u + δ (X.d2pi x τ e u) • e := by
  rw [unipotent_mulVec_formula, hyperbolic_coeff_b_apply, hu1]
  simp

lemma unipotent_on_hyperbolic_complement {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0)
    (hu2 : hermC τ.1 X.Gm u (X.Jp x τ e) = 0) :
    Matrix.mulVec (X.d2n x τ e δ) u = u + δ u • e := by
  rw [X.unipotent_on_orthogonal_e δ hx he hq hu1, X.hyperbolic_projection_of_perp hx he hq hu1 hu2]

lemma unipotent_transform_unitary (hqr : conj (X.d2q x τ e) = X.d2q x τ e) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.d2n x τ e δ) u) (Matrix.mulVec (X.d2n x τ e δ) w) =
      hermC τ.1 X.Gm u w := by
  have hb : ∀ v, hermC τ.1 X.Gm v e = X.d2q x τ e * X.d2b x τ e v := by
    intro v
    rw [hyperbolic_coeff_b_apply, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  have hz : ∀ v, hermC τ.1 X.Gm v (X.d2z x τ e δ) = X.d2q x τ e * δ (X.d2pi x τ e v) :=
    X.unipotent_shift_spec δ hx he hq
  have hze : hermC τ.1 X.Gm (X.d2z x τ e δ) e = 0 := X.unipotent_shift_orthogonal_e δ hx he hq
  have hez : hermC τ.1 X.Gm e (X.d2z x τ e δ) = 0 := by
    rw [X.hsym, hze, map_zero]
  have hew : ∀ v, hermC τ.1 X.Gm e v = X.d2q x τ e * conj (X.d2b x τ e v) := by
    intro v
    rw [X.hsym, hb, map_mul, hqr]
  have hzw : ∀ v, hermC τ.1 X.Gm (X.d2z x τ e δ) v =
      X.d2q x τ e * conj (δ (X.d2pi x τ e v)) := by
    intro v
    rw [X.hsym, hz, map_mul, hqr]
  have hzz := X.unipotent_shift_self_pairing δ hx he hq
  have hδ : conj (δ (X.d2z x τ e δ)) = δ (X.d2z x τ e δ) := by
    have h1 := X.hsym (τ := τ) (X.d2z x τ e δ) (X.d2z x τ e δ)
    rw [hzz, map_mul, hqr] at h1
    exact (mul_left_cancel₀ hq h1).symm
  rw [unipotent_mulVec_formula, unipotent_mulVec_formula]
  simp only [hC_add_left, hermC_sub_left_section, hC_smul_left, hermC_add_right_section, hC_sub_right,
    hermC_smul_right_section]
  simp only [he, hze, hez, hzz]
  simp only [hb, hz, hew, hzw]
  simp only [map_sub, map_mul, map_div₀, hδ, map_ofNat]
  ring

end perTau

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
