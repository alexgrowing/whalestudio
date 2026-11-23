import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

def secOpen (s : X → X → ℂ) : Set X := {y | s y y ≠ 0}

def rSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ := Real.exp 1 - 2 * logNormSec L s y

structure IsLemmaEPot (A : FinHolAtlas D X) (Om : KaehlerForm A) (L : LocPot X)
    (s : X → X → ℂ) (C₁ : ℝ) (u : X → ℝ) : Prop where
  smooth : A.SmoothOn (secOpen s) u
  nonneg : FormNonneg A (secOpen s) (potForm Om.pot u)
  nonpos : ∀ x ∈ secOpen s, u x ≤ 0
  le_u : ∀ x ∈ secOpen s, -(C₁ * Real.log (rSec L s x)) ≤ u x
  smooth_or_pole : A.Smooth u ∨ ∀ y, y ∉ secOpen s → Tendsto u (𝓝[secOpen s] y) atBot

def LemmaETailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailLogBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

section Inhabitants

open OnePoint
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection crd0 crd1 fsPot_φ_coe
  projLineSection_infty projLineSection_coe)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
