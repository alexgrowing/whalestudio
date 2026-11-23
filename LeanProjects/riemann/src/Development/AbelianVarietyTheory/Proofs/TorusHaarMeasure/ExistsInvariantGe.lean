import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicThreshold
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.CMTypeLowModes
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurablePhi

namespace GlobalTheory.FinVolModes

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.CMTypeLowModes (IsInvariant TwoBounds PointBound NoModesBelow LowModes Inputs)

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Covers (X : Data E r) (x y : Frame X.Ψ r) : Prop :=
  y ∈ X.dom ∧ X.la1 y = X.la1 x ∧ ∀ ξ, X.IsIso ξ → ∃ ξ', X.IsIso ξ' ∧ X.tt ξ' y = X.tt ξ x

theorem Covers.trans {X : Data E r} {x y z : Frame X.Ψ r} (h : Covers X x y) (h' : Covers X y z) :
    Covers X x z := by
  refine ⟨h'.1, h'.2.1.trans h.2.1, fun ξ hξ => ?_⟩
  obtain ⟨ξ1, h1, e1⟩ := h.2.2 ξ hξ
  obtain ⟨ξ2, h2, e2⟩ := h'.2.2 ξ1 h1
  exact ⟨ξ2, h2, e2.trans e1⟩

def hull (X : Data E r) (ps : Frame X.Ψ r → ℝ) (x : Frame X.Ψ r) : ℝ :=
  sSup (ps '' {y | Covers X x y})

end

end GlobalTheory.FinVolModes
