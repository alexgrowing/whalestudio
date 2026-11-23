import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocks
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  first | exact @GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | exact GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | (intros; apply GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl <;> assumption)
