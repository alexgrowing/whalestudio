import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def column {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) : Lt1 Dw →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

@[simp] theorem column_apply {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) (ℓ : Lt1 Dw) :
    column m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩ := rfl

section Value

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def canGerm (C : ChartAt Xo c y) (k : ℕ) (f : Germ.PS S 1 C.d) : Germ.PS S 1 C.d :=
  f * Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)

def colVal (C : ChartAt Xo c y) (k : ℕ) (f : Germ.PS S 1 C.d) (α : Lt1 Dw →₀ ℕ) : S :=
  MvPowerSeries.constantCoeff (Germ.DmonOf C.B.G.F C.uvec α (canGerm C k f))

def chartVal (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F)
    (f : Fin n → Germ.PS S 1 C.d) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, colVal C k (f b) (column m b)

example (C : ChartAt Xo c y) (k n : ℕ) (f : Fin n → Germ.PS S 1 C.d) :
    chartVal C k (0 : MvPolynomial (LtN Dw n) c.F) f = 0 := by
  simp [chartVal]

end Value

def harmType (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def ChartIndep (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
    (C₁ C₂ : ChartAt Xo c y) (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f₁ : Fin n → Germ.PS S 1 C₁.d) (f₂ : Fin n → Germ.PS S 1 C₂.d),
    (∀ b, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F b) (f₁ b)) →
    (∀ b, IsGerm y C₂.d C₂.x C₂.B.A.act C₂.e C₂.wP k (F b) (f₂ b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmType Dw c a n →
      chartVal C₁ k P f₁ = chartVal C₂ k P f₂

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms
