import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexPrimeMemNonunits
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem DifferentiableLines.nonempty_toroidal_flag_bundle : GlobalTheory.Published.ToroidalCompactification → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → Nonempty (GlobalTheory.CompHS.TorFlag Xo c) := by
  intro hP E _ _ _ H Dw l Xo c hd
  obtain ⟨Y, hs, hb, hk⟩ := hP E H Dw hd l Xo c
  exact GlobalTheory.CompHS.TorFlagEx.torFlag_of_model Y hs hb hk
    (GlobalTheory.CompHS.TorFlagEx.pushInvertible_of_hasTheta Y (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw hd l Xo c Y hs))
