import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section herm

variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hC_add_left (u u' v : Fin r → ℂ) : hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hC_sub_left (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma hC_smul_left (c : ℂ) (u v : Fin r → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_add_right (u v v' : Fin r → ℂ) : hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma hC_smul_right (c : ℂ) (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hC_add_left, ih]

lemma hC_symm (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc, hG]
  ring

lemma emb_herm (x y : Fin r → E) : τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by
  simp only [herm, hermC, Data.emb, map_sum, map_mul, emb_cc]

end herm

namespace Data

variable {r : ℕ} (X : Data E r)

lemma col_mul (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = Matrix.mulVec A (col B a) := by
  funext k; simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  funext a
  simp only [flowMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, emb, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

lemma ppos_eq_of (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (β : Fin X.p0 → ℂ)
    (horth : ∀ b : Fin X.p0, hermC τ.1 X.Gm (u - ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    X.ppos x τ u = ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a) := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have hc : cf = Matrix.vecMul β A := by
    funext b
    have h := horth b
    rw [hC_sub_left, sub_eq_zero, hC_sum_left] at h
    simp only [cf, h, hC_smul_left, Matrix.vecMul, dotProduct, hAdef, gramPos, gram,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hα : (fun a => ∑ b, cf b * A⁻¹ b a) = β := by
    have : Matrix.vecMul cf A⁻¹ = β := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.vecMul_one]
    rw [← this]; rfl
  unfold ppos
  rw [← hα]

lemma ppos_orth (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (b : Fin X.p0) : hermC τ.1 X.Gm (u - X.ppos x τ u) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have key : Matrix.vecMul (Matrix.vecMul cf A⁻¹) A = cf := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.vecMul_one]
  have h2 := congrFun key b
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [hC_sub_left, sub_eq_zero]
  unfold ppos
  rw [hC_sum_left]
  simp only [hC_smul_left]
  rw [show hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) = cf b from rfl, ← h2]
  rfl

lemma gramPos_det_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).det ≠ 0 := by
  have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  intro h0
  have : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
  rw [this] at h
  simp at h

end Data

end ReciprocityTheory.ChartRestriction.G.FD
