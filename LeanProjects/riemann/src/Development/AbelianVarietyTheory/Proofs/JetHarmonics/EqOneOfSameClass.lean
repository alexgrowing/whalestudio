import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UnitaryDetClass

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitaryRigid

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def hf (v w : Fin n → E) : E := ∑ j, IsCMField.complexConj E (v j) * w j

def qf (v : Fin n → E) : ℝ := ∑ σ : E →ₐ[ℚ] ℂ, ∑ j, ‖σ (v j)‖ ^ 2

end GlobalTheory.UnitaryRigid
