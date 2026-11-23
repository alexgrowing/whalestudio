import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensions
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_finite_values | exact GlobalTheory.Reg.sec_eq_zero_of_finite_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_finite_values <;> assumption)
