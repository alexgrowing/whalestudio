import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_log_height_formula : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : GlobalTheory.TrueGeo.Ext v) (y : AlgPt (O.var c)), (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).lg v e y = Real.log (e.w (valAt y.1 (genAt (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D (below y.1) / ∏ k : Fin (D.R.f * O.N), genAt (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D (below y.1) ^ (-1 : ℤ)))) - ∑ k : Fin (D.R.f * O.N), (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).lg v e y := by
  first | exact @GlobalTheory.CovolFin.lg_detOmSym | exact GlobalTheory.CovolFin.lg_detOmSym | (intros; apply GlobalTheory.CovolFin.lg_detOmSym <;> assumption)
