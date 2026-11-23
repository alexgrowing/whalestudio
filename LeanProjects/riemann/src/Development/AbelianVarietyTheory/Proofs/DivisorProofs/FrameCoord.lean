import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset

noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FrameCoord {K : Type} [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K)
    {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)} (m1 : SABMap t₀ Xo.univ.t y.x)
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ)
    (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K) : Prop :=
  ∀ i, ∃ (u : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A),
    u ≫ m1.φ = y.u ρ i ∧ u ≫ m2.φ = w.left ≫ F.φ ∧ IsLieComb (v i) F.v w

def LocBasis {K : Type} [Field K] [NumberField K] {n : ℕ} (𝔓 : HeightOneSpectrum (𝓞 K))
    (L : Submodule (𝓞 K) (Fin n → K)) {m : ℕ} (b : Fin m → Fin n → K) : Prop :=
  (∀ i, b i ∈ L) ∧ LinearIndependent K b ∧
    ∀ x ∈ L, ∃ d : 𝓞 K, d ∉ 𝔓.asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b)

end GlobalTheory.PtDeg
