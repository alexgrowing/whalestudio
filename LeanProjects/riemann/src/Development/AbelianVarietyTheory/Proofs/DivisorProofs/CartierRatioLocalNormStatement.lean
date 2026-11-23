import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierRatioLocalNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_ratio_local_norm : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ), lnAdl (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))) σ z = Real.log ‖GlobalTheory.Cartier.ratVal (genAt (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D (GlobalTheory.Cartier.under z) / ∏ k : Fin (D.R.f * O.N), genAt (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D (GlobalTheory.Cartier.under z) ^ (-1 : ℤ)) z‖ - ∑ k : Fin (D.R.f * O.N), lnAdl (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)) σ z := by
  first | exact @GlobalTheory.OmCx.om_cx | exact GlobalTheory.OmCx.om_cx | (intros; apply GlobalTheory.OmCx.om_cx <;> assumption)
