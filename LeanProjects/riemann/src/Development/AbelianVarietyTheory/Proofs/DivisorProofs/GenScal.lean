import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

noncomputable section

namespace GlobalTheory.LevModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Moved (X₂ X : Data E r) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) : Prop :=
  ∀ (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ),
    mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩

open Classical in

def genScal {S : Type} [CommRing S] (t : Sˣ) : Ix Dw → Sˣ := fun i => if i = none then t else 1

def Over (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E) : Prop :=
  ∀ (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom) (x' : Frame (U.X k).Ψ r), Moved (U₂.X k₂) (U.X k) δ x x' →
    ∃ hx' : x' ∈ (U.X k).dom, ∃ t : ℂˣ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖(t : ℂ)‖ = 1) ∧
      letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
      ∃ y : FrPt Xo c (CAt σ₂),
        FrBor (S := CAt σ₂) (genScal (Dw := Dw) (S := CAt σ₂) t) (U.un k ⟨x', hx'⟩) y ∧
        FrOver d (U₂.un k₂ ⟨x, hx⟩) y

end GlobalTheory.LevModel
