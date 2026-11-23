import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcDense

theorem eq_zero_of_eval_off {σ : Type} (D P : MvPolynomial σ ℂ) (hD : D ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x D ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have h0 : D * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD

noncomputable def coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K)) :
    MvPolynomial σ ℂ :=
  ∑ μ ∈ Q.support, MvPolynomial.monomial μ (ι ((Q.coeff μ).coeff j))

theorem coeff_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (ν : σ →₀ ℕ) : (coefPoly ι j Q).coeff ν = ι ((Q.coeff ν).coeff j) := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; simp

theorem eval_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (x : σ → ℂ) : MvPolynomial.eval x (coefPoly ι j Q) =
      ∑ μ ∈ Q.support, ι ((Q.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by
  rw [coefPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_eq_zero_of_vanish_on_invBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro E _ _ _ H Dw l Xo c K₁ _ _ d ι m a F h μ
  classical
  let D : MvPolynomial (ArcLt Dw) ℂ :=
    ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (ArcLt Dw) ℂ)).det
  have hDe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x D =
      ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det := by
    intro x
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp
  have hD : D ≠ 0 := by
    intro h0
    have h1 := hDe (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at h1
    have h2 : ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)) = 1 := by
        ext i k
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    simp only [h2, Finset.prod_const_one] at h1
    exact zero_ne_one h1
  let P : MvPolynomial (ArcLt Dw) ℂ :=
    ∑ i, MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))
  have hP : P = 0 := by
    refine eq_zero_of_eval_off D P hD fun x hx => ?_
    rw [hDe] at hx
    have hx' : InvBl x := fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ τ)
    rw [← h x hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, eval_coefPoly]
    rfl
  have := congrArg (MvPolynomial.coeff μ) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_coefPoly]
  rfl

end GlobalTheory.ArcDense
