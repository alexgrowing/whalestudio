import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormGoodPrimeIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomNormPIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormGoodPrimeIntegral.proof (hN : PullConeNullModP.Statement) (hD : PullConeDegreeInt.Statement)
    (hI : PullSectionIntegralInt.Statement) (hP : DehomNormPIntegral.Statement) :
    FibreNormGoodPrimeIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz p hp hgood τ s hs j c hc μ
  classical
  obtain ⟨N, M, hpM, hrel⟩ := hN K ι Ω y D L hz p hp hgood
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    obtain ⟨_, ⟨_, _, hrv⟩, _, _⟩ := hA
    obtain ⟨c', hc'⟩ := CoordArithOfFnField.nonzero_of_relevant y hrv
    exact fun k => ⟨c' k, hc' k⟩
  have hM : (M : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hpM (dvd_zero p))
  obtain ⟨hj, hfin, -, hch, hcp⟩ := hc
  have := hfin
  have hint := hI K ι Ω y D e L q N M hy he hL hM (hD K ι Ω y D e L N M hy hL hrel) τ s hs j hj
  have hgen := PullFormsGeneric.proof
    (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof)
    K ι Ω y D e L hA hB he hL hz
  exact hP Ω D (fun i => aeval y (L i)) (pullField y L) rfl hgen p hp M hpM j (q * τ) _ hint c
    (hch _ le_rfl) hcp μ

end GroundTheory.Heights₂.Heights.HilbertSamuel
