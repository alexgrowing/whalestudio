import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ
open scoped ComplexConjugate

namespace GlobalTheory.FJCuspCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem cc_kappa (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h := X.ξ0_im
  unfold cc at h ⊢
  rcases X.κ0_xi with h' | h' <;> rw [h'] <;> simp [h, map_ofNat]

noncomputable def ev (χ : Matrix (Fin ρ) (Fin ρ) E) (u u' : Fin ρ → E) : E :=
  ∑ a, ∑ b, u a * χ a b * cc (u' b)

noncomputable def gen (X : Data E r) (b : E) (u u' : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) E :=
  Matrix.of fun i k => X.κ0 / 2 * (b * u i * cc (u' k) + cc b * u' i * cc (u k))

theorem pair_real (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) (hχ : IsHermE χ) (hβ : IsSkew β) :
    cc (Matrix.trace (χ.transpose * β) / (X.κ0 / 2)) = Matrix.trace (χ.transpose * β) / (X.κ0 / 2) := by
  have hk := cc_kappa X
  have ht : cc (Matrix.trace (χ.transpose * β)) = -Matrix.trace (χ.transpose * β) := by
    have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
    have h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hβ
    simp only [cc, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, map_sum,
      map_mul, h1, h2, mul_neg, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  unfold cc at hk ht ⊢
  rw [map_div₀, map_div₀, hk, ht, map_ofNat, neg_div 2 X.κ0, neg_div_neg_eq]

def cuspOfIso (X : Data E r) (ξ : Fin r → E) (h0 : ξ ≠ 0) (hi : herm X.Gm ξ ξ = 0) : CuspFD X 1 where
  e := fun _ => ξ
  ind := linearIndependent_unique_iff.2 h0
  iso := fun _ _ => hi

end GlobalTheory.FJCuspCheck
