import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionEqZeroOfIncreasingFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (τ : E →+* ℂ) (i j : Fin (Dw.mult τ)), i < j → e (some ⟨τ, i⟩) < e (some ⟨τ, j⟩) → ∀ f ∈ secZ Xo c e, f = 0 := by
  first | exact @GlobalTheory.IncrZero.secZ_eq_zero_of_lt | exact GlobalTheory.IncrZero.secZ_eq_zero_of_lt | (intros; apply GlobalTheory.IncrZero.secZ_eq_zero_of_lt <;> assumption)
