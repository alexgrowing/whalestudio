import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ChartIndepSt2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S),
    (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) →
    (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      chartVal C k f P = chartVal C' k f' P

theorem thExprUniq_of_chartIndep2 (hC : ChartIndepSt2) : ThExprUniqSt := by
  intro E _ _ _ H Dw l Xo c _ nab₁ nab₂ h₁ h₂ S _ _ _ y k n F a P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := h₁.2 S y
  obtain ⟨C₂, hex₂, hpin₂⟩ := h₂.2 S y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  choose f₂ hf₂ using fun b => hex₂ k (F b)
  have e₁ : ∀ m, ∏ b, nab₁ y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal S C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab₂ y k (F b) (colOf m b) =
      ∏ b, C₂.B.nabVal S C₂.h H.w0 k (f₂ b) C₂.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₂ k (F b) (f₂ b) (hf₂ b) (colOf m b)
  have h := hC E H Dw l Xo c h₁.1 S y C₁ C₂ k n F f₁ f₂ hf₁ hf₂ a P hP
  simp only [chartVal] at h
  simp only [e₁, e₂]
  exact h

end Formalism.MainNotions.ModuliIntegralCharts.H1
