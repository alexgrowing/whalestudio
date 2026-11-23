import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefF
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedRestrict
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedNefF.proof : GeneratedNefF.Statement := by
  intro F _ K _ _ ι _ _ I V a hI hgen W hW hVW
  have hgW : KH.GeneratedV F W a := GeneratedRestrict.proof F K ι V W a hVW hgen
  exact GeneratedProductNonneg.proof GeneratedRestrict.proof GeneratedEffectiveSection.proof
    F K ι I W 1 ![a] hI hW (Fin.forall_fin_one.mpr hgW)

end GroundTheory.Heights₂.Heights.HilbertSamuel
