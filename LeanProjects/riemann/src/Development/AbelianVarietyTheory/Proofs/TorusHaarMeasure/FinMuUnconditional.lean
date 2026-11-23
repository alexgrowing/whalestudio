import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLatticeStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.DriftCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finMu_unconditional : ∀ (r : ℕ) (X : Data E r), FinMu X :=
  GlobalTheory.ClosedFiniteMeasure.finMu_of_covolume GlobalTheory.T.exists_finite_measure_cover_unitary_lattice

end GlobalTheory.DriftCovolume
