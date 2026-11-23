import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := NumberField.IsCMField.complexEmbedding_complexConj E τ x

section herm

variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hermC_add_left (u u' v : Fin r → ℂ) : hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hermC_add_right (u v v' : Fin r → ℂ) : hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma hermC_smul_left (a : ℂ) (u v : Fin r → ℂ) : hermC τ G (a • u) v = a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hermC_smul_right (a : ℂ) (u v : Fin r → ℂ) : hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hermC_conj (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    conj (hermC τ G u v) = hermC τ G v u := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc' τ (G b a), hG]
  ring

lemma hermC_emb (x y : Fin r → E) :
    hermC τ G (fun a => τ (x a)) (fun a => τ (y a)) = τ (herm G x y) := by
  simp only [hermC, herm, map_sum, map_mul, emb_cc']

end herm

section flowAlg

variable (X : Data E r)

def wv (ξ : Fin r → E) (τ : X.Ψ) : Fin r → ℂ := fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))

lemma wv_dot (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) :
    wv X ξ τ ⬝ᵥ v = hermC τ.1 X.Gm v (Data.emb τ.1 ξ) := by
  simp only [dotProduct, wv, hermC, Data.emb, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma wv_dot_self {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    wv X ξ τ ⬝ᵥ Data.emb τ.1 ξ = 0 := by
  rw [wv_dot]
  exact (hermC_emb τ.1 X.Gm ξ ξ).trans (by rw [hξ, map_zero])

lemma flowMat_eq (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) :
    X.flowMat ξ τ s = 1 + (-(I * X.c τ * s)) • vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    vecMulVec_apply, wv, Data.emb, smul_eq_mul]
  ring

lemma nil_sq {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) * vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) = 0 := by
  ext a b
  have h0 := wv_dot_self X hξ τ
  simp only [dotProduct] at h0
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  calc ∑ k, Data.emb τ.1 ξ a * wv X ξ τ k * (Data.emb τ.1 ξ k * wv X ξ τ b)
      = Data.emb τ.1 ξ a * wv X ξ τ b * ∑ k, wv X ξ τ k * Data.emb τ.1 ξ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = 0 := by rw [h0, mul_zero]

lemma flowMat_mul {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s s' : ℂ) :
    X.flowMat ξ τ s * X.flowMat ξ τ s' = X.flowMat ξ τ (s + s') := by
  rw [flowMat_eq, flowMat_eq, flowMat_eq]
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, nil_sq X hξ,
    smul_zero, smul_zero, add_zero, add_assoc, ← add_smul]
  congr 2
  ring

lemma flowMat_zero (ξ : Fin r → E) (τ : X.Ψ) : X.flowMat ξ τ 0 = 1 := by
  ext a b
  simp [Data.flowMat, Matrix.one_apply]

lemma det_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det = 1 := by
  rw [flowMat_eq, Matrix.vecMulVec_eq Unit, ← Matrix.smul_mul, ← Matrix.replicateCol_smul,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, wv_dot_self X hξ,
    smul_zero, add_zero]

lemma flow_flow {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s s' : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s (X.flow ξ s' x) = X.flow ξ (s + s') x := by
  funext τ
  show (X.flowMat ξ τ (s τ) * (X.flowMat ξ τ (s' τ) * mat x τ) : Matrix (Fin r) (Fin r) ℂ) =
    X.flowMat ξ τ ((s + s') τ) * mat x τ
  rw [← Matrix.mul_assoc, flowMat_mul X hξ, Pi.add_apply]

lemma flow_zero (ξ : Fin r → E) (x : Frame X.Ψ r) : X.flow ξ 0 x = x := by
  funext τ
  show (X.flowMat ξ τ ((0 : X.Ψ → ℂ) τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Pi.zero_apply, flowMat_zero, Matrix.one_mul]
  rfl

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ v = v + ((-(I * X.c τ * s)) * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) •
      Data.emb τ.1 ξ := by
  rw [flowMat_eq, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  rw [← wv_dot X ξ τ v]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end flowAlg

end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
