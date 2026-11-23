import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralComb_idempotentSections_nonneg_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  first | exact @GlobalTheory.IdemInt.idem_comb_mul_nonneg | exact GlobalTheory.IdemInt.idem_comb_mul_nonneg | (intros; apply GlobalTheory.IdemInt.idem_comb_mul_nonneg <;> assumption)
