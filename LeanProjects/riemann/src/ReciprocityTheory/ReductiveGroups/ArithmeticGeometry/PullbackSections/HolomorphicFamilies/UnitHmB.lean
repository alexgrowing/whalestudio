import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem tau_cc (τ : E →+* ℂ) (y : E) : τ (cc y) = conj (τ y) :=
  NumberField.IsCMField.complexEmbedding_complexConj E τ y

theorem hermC_mulVec' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (y v : Fin r → ℂ) :
    hermC τ G (x.mulVec y) v = ∑ a, y a * hermC τ G (col x a) v := by
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem hermC_symm' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (u v : Fin r → ℂ) : hermC τ G u v = conj (hermC τ G v u) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h1 : conj (τ (G a b)) = τ (G b a) := by rw [← tau_cc, hG]
  rw [h1]
  ring

theorem ortho_gram' (X : Data E r) (x : Frame X.Ψ r) (hx : X.IsOrtho x) (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0 := by
  have := congrFun (congrFun (hx τ) a) b
  simp only [gram, Matrix.of_apply, Matrix.diagonal_apply] at this
  rw [this]

theorem tau_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v w : Fin r → E) :
    τ (herm G v w) = hermC τ G (Data.emb τ v) (Data.emb τ w) := by
  simp only [herm, hermC, Data.emb, map_sum, map_mul, tau_cc]

theorem hermC_mulVec_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (x : Matrix (Fin r) (Fin r) ℂ) (u y : Fin r → ℂ) :
    hermC τ G u (x.mulVec y) = ∑ b, conj (y b) * hermC τ G u (col x b) := by
  rw [hermC_symm' τ G hG, hermC_mulVec', map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, ← hermC_symm' τ G hG]

variable (X : Data E r) (x : Frame X.Ψ r)

def cv (τ : X.Ψ) (v : Fin r → E) : Fin r → ℂ := (mat x τ)⁻¹.mulVec (Data.emb τ.1 v)

theorem emb_eq (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (v : Fin r → E) :
    Data.emb τ.1 v = (mat x τ).mulVec (cv X x τ v) := by
  rw [cv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem hermC_coord (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (v w : Fin r → E) :
    hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w) =
      ∑ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * cv X x τ v a * conj (cv X x τ w a) := by
  rw [emb_eq X x τ hdet v, emb_eq X x τ hdet w, hermC_mulVec']
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_mulVec_right τ.1 X.Gm X.Gm_herm]
  simp only [ortho_gram' X x hx, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem hermC_col_emb (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (v : Fin r → E) (b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) b) (Data.emb τ.1 v) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * conj (cv X x τ v b) := by
  rw [emb_eq X x τ hdet v, hermC_mulVec_right τ.1 X.Gm X.Gm_herm]
  simp only [ortho_gram' X x hx, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
