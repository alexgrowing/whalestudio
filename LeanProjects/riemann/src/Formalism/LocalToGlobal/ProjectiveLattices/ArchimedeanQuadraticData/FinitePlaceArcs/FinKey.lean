import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FinAtOfStatement

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FreeQuotientRank MvPolynomial

namespace FinKey

theorem bind₁_scale_monomial {ι R : Type} [CommRing R] (a : ι → R) (ν : ι →₀ ℕ) (r : R) :
    bind₁ (fun x => C (a x) * X x) (monomial ν r) = monomial ν (r * ν.prod fun x e => a x ^ e) := by
  rw [bind₁_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, map_mul, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, map_pow]
  ring

theorem coeff_bind₁_scale {ι R : Type} [CommRing R] (a : ι → R) (q : MvPolynomial ι R) (μ : ι →₀ ℕ) :
    coeff μ (bind₁ (fun x => C (a x) * X x) q) = (μ.prod fun x e => a x ^ e) * coeff μ q := by
  classical
  refine MvPolynomial.induction_on' q ?_ ?_
  · intro ν r
    rw [bind₁_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  · intro p q hp hq
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def detZ (Dw : Datum H) : MvPolynomial (ArcLt Dw) ℤ :=
  ∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => (X (⟨τ, i, l⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℤ)).det

open Classical in

def subA {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (y x : ArcLt Dw) : K :=
  ∑ k : Fin (Dw.mult y.1), if x = ⟨y.1, y.2.1, k⟩ then A y.1 k y.2.2 else 0

theorem subA_sum {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (y : ArcLt Dw) :
    (∑ x : ArcLt Dw, C (subA A y x) * (X x : MvPolynomial (ArcLt Dw) K)) =
      ∑ k : Fin (Dw.mult y.1), C (A y.1 k y.2.2) * X ⟨y.1, y.2.1, k⟩ := by
  simp only [subA, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single ⟨y.1, y.2.1, k⟩]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end FinKey

end Formalism.L2.Pj.QAt
