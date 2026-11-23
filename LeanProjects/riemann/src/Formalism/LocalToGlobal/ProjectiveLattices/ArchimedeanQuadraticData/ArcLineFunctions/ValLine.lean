import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def lineVal (n : ℕ) (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (μ : ArcLt Dw →₀ ℕ) : ℤ :=
  -((n : ℤ) * vth) - ∑ x ∈ μ.support, (μ x : ℤ) * vη x.1 x.2.2

end Formalism.L2.Pj.QAt
