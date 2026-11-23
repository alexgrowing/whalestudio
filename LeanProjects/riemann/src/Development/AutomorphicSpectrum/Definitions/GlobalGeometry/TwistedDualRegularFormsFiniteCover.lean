import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ChartSpec

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def fundF (X : Data E r) : Set (V (nd X)) :=
  if h : ∃ FF, IsFundSet X (x0F X) FF then h.choose else ∅

def petU (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) : ℂ :=
  ∫ z in fundF X, P (cpt X (x0F X) z) * (starRingEnd ℂ) (Q (cpt X (x0F X) z)) *
    ((X.nfac la (cpt X (x0F X) z) ^ 2 : ℝ) : ℂ) ∂muF X (x0F X)

def pet (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) : ℂ :=
  petU X la P Q / (((covol X).toReal : ℝ) : ℂ)

end GlobalTheory.CompanionTheory.Ar.Deg
