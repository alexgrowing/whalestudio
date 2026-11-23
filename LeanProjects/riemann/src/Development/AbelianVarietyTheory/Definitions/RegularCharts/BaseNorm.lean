import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd

noncomputable section

namespace GlobalTheory.FrameNorm

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsUnitFr {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Prop := ∀ τ i, ‖dmin X.Gm x τ i‖ = 1

def baseNorm (Dw : Datum H) (x : ℝ) : Ix Dw → ℝ
  | none => 1
  | some _ => Real.sqrt (2 * Real.pi * x)

def conjAlg {K : Type} [Field K] (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }

def FnPin {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (x : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop :=
  (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (z : ((U σ).X k).dom), IsUnitFr ((U σ).X k) z.1 →
    ∀ (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k z) y →
      ∀ i, |fn σ y i| = cabs (t i : CAt σ) * baseNorm Dw x i) ∧
  ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))),
    FrMap (conjAlg σ) y y' → ∀ i, |fn _ y' i| = |fn σ y i|

def HasPrinc {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (M : ℕ) : Prop :=
  ∀ k (γ : GL (Fin r) E), IsUStab (U.X k).Gm (U.X k).Λ γ →
    (∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) →
      γ ∈ (U.X k).Γ

end GlobalTheory.FrameNorm
