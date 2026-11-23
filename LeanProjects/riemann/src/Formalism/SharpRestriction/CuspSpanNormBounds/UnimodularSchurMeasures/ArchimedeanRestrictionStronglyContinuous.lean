import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrcTendstoVec

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepInf (X : CData) : Prop := ∀ F : X.L2, Continuous fun g : X.I.Ginf => X.R (g, 1) F

theorem archimedean_restriction_strongly_continuous (X : CData) (hd : RegData X) (hu : UnimodA X) : RepInf X := by
  intro F
  have hH : X.μf.IsHaarMeasure := hd.1
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SecondCountableTopology X.L2 := automorphic_L2_secondCountable X
  obtain ⟨h1, h2, h3⟩ := rightRegular_isometric_multiplicative X hd hu
  refine rr_cont_of_meas (G := X.I.Ginf) (μ := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v))
    (π := fun g => X.R (g, 1)) (fun g h => ?_) h2 (fun g x => h3 _ x) (fun x y => ?_) F
  · rw [← h1]
    congr 1
    simp
  · exact ((regular_rep_coeff_measurable X hd hu x y).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable

end Formalism.MainNotions.LeviCoordinates

end
