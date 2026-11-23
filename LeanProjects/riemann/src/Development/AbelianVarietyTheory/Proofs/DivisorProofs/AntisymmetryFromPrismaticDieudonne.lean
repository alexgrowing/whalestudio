import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogSwapSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSymmetricImpliesSwapFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapFlagDegreeIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleStatementOfPrismaticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapFlagArithDegreeChernStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowLinAddCompEqZero
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.AntiFinite

theorem main : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → AntiSt := by
  intro hP2 hPH hRA hSW hPD
  have hAr : ArCalc := hP2.p4
  obtain ⟨G, hG, hG2⟩ := GlobalTheory.T.exists_homog_swap_symmetric hAr hRA
  have hFl : SwapFl G := GlobalTheory.T.swap_symmetric_implies_swap_flag hAr G hG hG2
  have hBun : BunSt := by apply GlobalTheory.T.bundle_statement_of_prismatic <;> assumption
  have hX := GlobalTheory.T.swap_flag_arith_degree_chern hP2 hPH hRA hBun G hG hFl
  have hMu := GlobalTheory.T.weights_sum_to_volume_proportional hP2 hPH
  intro D O hCore hf A T H hR hh hIs Φ hΦ
  exact GlobalTheory.CovTest.antisym_of_swapEq D O.Y Φ hh G hΦ (hMu D O hCore hf A T H hR).2.2
    (GlobalTheory.T.swap_flag_degree_identity hP2 hPH.deg G hG hFl D O.Y hh hIs) (hX D O hCore hf A T H hR)

end GlobalTheory.AntiFinite
