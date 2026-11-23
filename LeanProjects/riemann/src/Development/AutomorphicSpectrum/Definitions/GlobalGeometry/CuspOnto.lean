import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec

namespace GlobalTheory.CompanionTheory.Ar.ThA

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

def CuspOnto {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ σ : c.F →+* ℂ, GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k : (U σ).Comp,
    ∀ P ∈ ((U σ).X k).SS (laU (U σ) a n k), ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c),
      (∀ i, fs i ∈ cusp Xo c U a n) ∧ ∀ x ∈ ((U σ).X k).dom, P x = ∑ i, as i * rdU (U σ) (fs i) k x

end GlobalTheory.CompanionTheory.Ar.ThA
