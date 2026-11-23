import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdditiveRelations

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}
  {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {g : ℕ}

structure TieBy (A : TorusAt X x) (w0 : 𝓞 E) (φ : La ≃ₗ[𝓞 E] X.Λ) (Pm : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ θ : (Fin g → ℂ) → ℂ)
    (β : (Fin g → ℂ) →ₛₗ[starRingEnd ℂ] Vsp A.T.dim) : Prop where

  unit : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1
  bij : Function.Bijective β

  lattice : ∀ a, β (Pm a) = A.φ (φ a : Fin r → E)

  form : ∀ z w, hermForm Hm z w = starRingEnd ℂ (Hf (β z) (β w))

  theta : ∀ z, θ z = starRingEnd ℂ (A.s fun _ => β z)

  semi : ∀ a, χ (Pm a) = (A.T.eps (β (Pm a)) : ℂ)

  rankOne_base_weight_eq_cmTheta : A.w0 = w0

def Comparison₂ (A : TorusAt X x) (w0 : 𝓞 E) (φ : La ≃ₗ[𝓞 E] X.Λ) (Pm : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∃ β : (Fin g → ℂ) →ₛₗ[starRingEnd ℂ] Vsp A.T.dim, TieBy A w0 φ Pm Hm χ θ β

def FramePhase (A : TorusAt X x) : Prop :=
  ∀ τ a, hermC τ.1 X.Gm (col (mat x τ) a) (A.e τ a) = ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)

namespace TieBy

variable {A : TorusAt X x} {w0 : 𝓞 E} {φ : La ≃ₗ[𝓞 E] X.Λ} {Pm : La →+ (Fin g → ℂ)}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ θ : (Fin g → ℂ) → ℂ}
  {β β' : (Fin g → ℂ) →ₛₗ[starRingEnd ℂ] Vsp A.T.dim}

end TieBy

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdditiveRelations
