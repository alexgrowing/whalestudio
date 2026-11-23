import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.DimAddCardFlagVar
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem fnFG_fnTrdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FnFG Xo c ∧ FnTrdeg Xo c (Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨h1, h2⟩ := GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c
  refine ⟨fnFG_of Xo c h1, ?_⟩
  rw [← dim_add_card_flagVar E H Dw]
  exact fnTrdeg_of Xo c Dw.dim h2

end GlobalTheory.FlagDim
