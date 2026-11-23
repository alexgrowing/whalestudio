import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace FormalGroupOnCopies

def OnCopies {k : Type} [CommRing k] {n d : ℕ} (S : Finset (Fin n)) (f : PS k n d) : Prop :=
  ∀ mm : Fin n × Fin d →₀ ℕ, coeff mm f ≠ 0 → ∀ i ∈ mm.support, i.1 ∈ S

end FormalGroupOnCopies

open FormalGroupOnCopies

def ColumnsStatement : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O),
    constantCoeff (B.hL k h w0) = 0 →
    ∀ (m n : ℕ) (S : Finset (Fin n)) (f₁ f₂ : PS k n d) (ι : Type) [Fintype ι]
      (cp : ι → Fin n) (u : ι → Fin d → k) (P₁ P₂ : MvPolynomial ι k),
      OnCopies S f₁ → OnCopies Sᶜ f₂ → (∀ l ∈ P₁.vars, cp l ∈ S) → (∀ l ∈ P₂.vars, cp l ∉ S) →
      nabValN B k h w0 m (f₁ * f₂) cp u (P₁ * P₂) =
        nabValN B k h w0 m f₁ cp u P₁ * nabValN B k h w0 m f₂ cp u P₂

end Formalism.MainNotions.ModuliIntegralCharts.H1
