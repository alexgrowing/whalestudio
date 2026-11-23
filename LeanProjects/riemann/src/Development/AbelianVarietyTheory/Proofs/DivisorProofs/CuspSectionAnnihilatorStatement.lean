import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_section_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  first | exact @GlobalTheory.FlatCore.cuspOn_cancel | exact GlobalTheory.FlatCore.cuspOn_cancel | (intros; apply GlobalTheory.FlatCore.cuspOn_cancel <;> assumption)
