import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionFlagEigenvalueStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.TestValOfHhTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAtOfPrismaticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourthPowerSumAtObjectsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePowerSumAndSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamAtOfCh2ConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Ch2HodgeVanishesOfPoincareStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.TestClassObj

theorem main : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd →
    PoincareDeRhamDuality → (∃ r, Ch2Const r) → TestSt := by
  intro hX h2 hH hR hSW hPr hPD hC
  obtain ⟨r, hr⟩ := hC
  have hV := GlobalTheory.T.ch2HodgeVanishes_of_poincareDeRhamDuality hX h2 hPD
  refine ⟨r, fun D O hO hf A T H h hh hhh Φ hΦ => ?_⟩
  have hz := GlobalTheory.T.hodge_tate_power_sum_and_siegel h2 hH hR hSW D O hO hf A T H h
  exact GlobalTheory.CovTest.testVal_of_hhTest r D O.Y Φ hh hf hΦ (GlobalTheory.T.weights_sum_to_volume_proportional h2 hH D O hO hf A T H h).2.2
    (by rw [HhTest, GlobalTheory.T.test_function_flag_eigenvalue h2 hH.deg h2.p4 hR D O.Y hh hhh, bcFl]; ring) (GlobalTheory.T.lattice_at_of_prismatic h2 hH hR hSW hPr D O hO hf A T H h)
    (GlobalTheory.T.fourth_power_sum_at_objects hX h2 hH hR hSW hPr D O hO hf A T H h) hz.1 hz.2 (GlobalTheory.T.de_rham_at_of_ch2_constant hSW hX h2 hH hR hV r hr D O hO hf A T H h)

end GlobalTheory.TestClassObj
