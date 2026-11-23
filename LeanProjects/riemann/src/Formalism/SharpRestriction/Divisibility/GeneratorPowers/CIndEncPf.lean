import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace CIndEncPf

theorem colSum_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (τ : E →+* ℂ) (hτ : InPsi H τ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
      (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
  have h0 := hP.1.1
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h0
  have h1 := h0 τ hτ i i'
  rw [← h1]
  simp only [lap, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [LinearMap.sum_apply]
  rfl

end CIndEncPf

open CIndEncPf in
theorem harmLink_holds : HarmLinkSt := by
  intro E _ _ _ H Dw l c a n P hP τ hτ i i'
  have key : ∀ b : Fin n,
      MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b)
        (MvPolynomial.pderiv (((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b)
          (encP P)) =
      MvPolynomial.rename (ltEquiv Dw n) (MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
        (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P)) := by
    intro b
    unfold encP
    rw [show (((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b) =
        ltEquiv Dw n ⟨ComplexEmbedding.conjugate τ, i', b⟩ from rfl,
      ← MvPolynomial.pderiv_rename (ltEquiv Dw n).injective,
      show (((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b) = ltEquiv Dw n ⟨τ, i, b⟩ from rfl,
      ← MvPolynomial.pderiv_rename (ltEquiv Dw n).injective]
  simp_rw [key]
  rw [← map_sum, colSum_zero c a n P hP τ hτ i i', map_zero]

theorem colLink_holds : ColLinkSt := by
  intro E _ _ _ H Dw n m b
  ext ℓ
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1
