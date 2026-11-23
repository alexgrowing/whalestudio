import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem cuspForms_finiteDimensional_of_goodEmb :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ) → Formalism.L2.Pj.CuspFD Xo c U := by
  intro E _ _ _ H Dw l Xo c r U σ hσ hU
  exact (Formalism.L2.PjFree.cuspFD_ofPj U).1
    (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ)
      ((Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 hU))

end GlobalTheory
