import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedDetDivergenceMemIdeal
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem psco_t_core : GlobalTheory.PsCo.Cw2a.CoreCondition := by
  intro A _ _ I _ _ D dm J Z u η E μ r h1 h2 h3 h4 h5
  exact GlobalTheory.weighted_det_divergence_mem_ideal (K := ℂ) D dm J Z u η E μ r h1 h2 h3 h4 h5

end GlobalTheory
