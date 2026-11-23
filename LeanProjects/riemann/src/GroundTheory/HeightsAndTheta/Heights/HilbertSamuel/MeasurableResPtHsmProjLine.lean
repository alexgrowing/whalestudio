import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def ResChiSymMeasure.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    Measurable (resPt d) → ∀ n : ℕ,
      resChi d n = chi d.x d.m (IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV) n

def ResolutionL2SymmetricMeasure.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    Measurable (resPt d) → ∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ), f.IsHomogeneous n →
      resolutionSectionL2Norm d n f = IndefiniteRowSideFullHecke.HilbertSamuel.secNorm d.x d.m (IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV) n
        (aeval d.x f)

namespace ProjLine

attribute [local instance] projectiveLineMeasurableSpace

theorem measurable_resPt_hsmProjLine : Measurable (resPt hsmProjLine) := by
  show Measurable fun x : OnePoint ℂ => ProjectiveLineResolution.lift x x
  refine measurable_of_continuousOn_compl_singleton OnePoint.infty ?_
  have hc : ContinuousOn crd0 ({OnePoint.infty}ᶜ : Set (OnePoint ℂ)) := by
    rw [OnePoint.compl_infty]
    exact continuousOn_finiteCoord
  have hv : ContinuousOn (fun x : OnePoint ℂ => ProjectiveLineResolution.vec 1 (crd0 x)) {OnePoint.infty}ᶜ := by
    refine continuousOn_pi.2 fun q => ?_
    obtain ⟨⟨⟩, i⟩ := q
    fin_cases i
    · exact continuousOn_const
    · exact hc
  refine hv.congr fun x hx => ?_
  have hx' : x ≠ OnePoint.infty := hx
  simp [ProjectiveLineResolution.lift, hx']

theorem ResChiSymMeasure.hyps_inhabited :
    ∃ d : HSMDatum 1 FnField (Fin 2), Measurable (resPt d) :=
  ⟨hsmProjLine, measurable_resPt_hsmProjLine⟩

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
