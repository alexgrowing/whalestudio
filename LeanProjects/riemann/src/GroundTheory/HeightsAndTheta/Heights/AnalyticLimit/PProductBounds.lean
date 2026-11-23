import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PDivisorNull
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StProductBounds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLogSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable isPotentialAdd
  isPotential_ofFun mIntCongrNull massIndep mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem ProductBounds.proof (hM : ListProductMass.Statement) (hT : ListTailLogSmooth.Statement) :
    ProductBounds.Statement := by
  intro D X _ _ _ A R Om C₁
  obtain ⟨CE, hCE⟩ := hT A R Om C₁
  refine ⟨Om.vol, CE, fun th u hf => ⟨?_, hCE th u hf⟩⟩
  have hpot : ∀ i, IsPotential A (potForm (th i) (u i)) := fun i =>
    isPotentialAdd A _ _ (hf i).1.th_pot (isPotential_ofFun A _ (hf i).2)
  have hnull := DivisorNull.proof A R
  have hind : mInt A (fun i => potForm (th i) (u i)) (R.Yo.indicator 1) =
      mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) :=
    mIntCongrNull A _ R.Yoᶜ hnull.1 hnull.2 _ _ fun x hx => by
      have hx' : x ∈ R.Yo := by simpa using hx
      simp [Set.indicator_of_mem hx']
  have hstokes : mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) = mInt A th (fun _ => 1) :=
    massIndep A th u (fun i => (hf i).1.th_pot) (fun i => (hf i).2)
  refine ⟨?_, hind.trans hstokes, ?_⟩
  · intro j K hK hKc
    have h1 := mIntegrableCont A _ hpot (fun _ => (1 : ℝ)) continuous_const j K hK hKc
    have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target R.isOpen_Yo
    refine (h1.indicator hO.measurableSet).congr_fun (fun y hy => ?_) hKc.measurableSet
    by_cases hy' : (A.chart j).symm y ∈ R.Yo
    · have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := ⟨hK hy, hy'⟩
      simp [Set.indicator_of_mem hyO, Set.indicator_of_mem hy']
    · have hyO : y ∉ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := fun h => hy' h.2
      simp [Set.indicator_of_notMem hyO, Set.indicator_of_notMem hy']
  · rw [← hstokes]
    exact hM A R Om C₁ th u hf

end GroundTheory.Heights₂.Heights.AnalyticLimit
