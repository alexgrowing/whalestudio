import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def LieFacAddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (x : ℝ)
    (a a' : (E →+* ℂ) × ℕ → ℕ), lieFac Dw x (a + a') = lieFac Dw x a * lieFac Dw x a'

def PnormMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r)
    (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r), x ∈ X.dom →
      X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x

def SupCMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (σ : c.F →+* ℂ)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), GoodEmb c σ → Even n → Even n' →
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ → supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) ≠ ⊤ →
      supC Xo c U x σ (a + a') (n + n') (f * g) ≤ supC Xo c U x σ a n f * supC Xo c U x σ a' n' g

def RecSubMulSt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (recPJ h j hj)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
