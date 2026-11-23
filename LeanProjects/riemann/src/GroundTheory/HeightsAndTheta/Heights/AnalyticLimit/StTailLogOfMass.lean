import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergySum
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable locDens)

noncomputable section

def shellConst (D : ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k

def TailLogOfMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (th : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → ContinuousOn r Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → IsPotential A th → (∀ i, A.SmoothOn Yo (u i)) →
    (∀ i, FormNonneg A Yo (potForm th (u i))) → ∀ CE : ℝ,
    TailMassBound A Yo r (fun i => potForm th (u i)) CE →
    TailLogBound A Yo r (fun i => potForm th (u i)) (shellConst D * CE)

section Inhabitants

open ReciprocityTheory.AnForm (fsDens fsDens_pos levi)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic projectiveLine_fubiniStudy_mass_one)
open ReciprocityTheory.AnForm.M.PLC (locDens_congr_phi mInt_congr_phi)

theorem potForm_fsPot_zero_φ (i : Fin 1) (a b : OnePoint ℂ) :
    ((fun _ : Fin 1 => potForm fsPot fun _ => (0 : ℝ)) i).φ a b = ((fun _ : Fin 1 => fsPot) i).φ a b :=
  add_zero _

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
