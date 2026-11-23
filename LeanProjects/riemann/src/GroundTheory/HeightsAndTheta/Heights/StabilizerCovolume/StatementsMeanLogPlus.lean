import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ULogBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree MeasureTheory
open scoped Matrix

def HasSpanningBound (Em : Type) [Field Em] [NumberField Em] (vr : ℝ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → 𝓞 Em), Submodule.span ℚ (Set.range fun i => (a i : Em)) = ⊤ ∧
    ∀ (σ : Em →+* ℂ) (i : Fin m), ‖σ (a i)‖ ≤ vr

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def isoCount (t : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ({v | v ∈ D.herm.L ∧ v ≠ 0 ∧ hermForm Em D.herm.H v v = 0 ∧ D.hodgeNormSq z v < t ^ 2}.ncard : ℝ)

def meanX (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu D.mu) g / degMu D.mu

abbrev XoPts : Type := {z : (Σ k, ι k) → ℂ // z ∈ D.Xo}

end FullerData

def IsTorusInv {K : Type} {ι : K → Type} (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ z, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → g (torusSmul c z) = g z

section Statements

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def MeanLogPlus.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  3 * D.j' + 1 ≤ D.N → ∀ vr : ℝ, HasSpanningBound Em vr →
    D.meanX (fun z => max 0 (Real.log (vr ^ (-(1 / 2 : ℝ)) / D.lam1 z))) ≤ 3

def InvariantMean.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∃ ν : Measure D.XoPts, IsProbabilityMeasure ν ∧
    (∀ t : ℝ, 0 < t → Integrable (fun z : D.XoPts => D.isoCount t z) ν) ∧
    ∀ g : ((Σ k, ι k) → ℂ) → ℝ, IsTorusInv g → Integrable (fun z : D.XoPts => g z) ν →
      D.meanX g = ∫ z, g z ∂ν

def FirstMinPos.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ z ∈ D.Xo, 0 < D.lam1 z

def CountMeasurable.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  Measurable (fun z : D.XoPts => D.lam1 z) ∧ ∀ t : ℝ, Measurable (fun z : D.XoPts => D.isoCount t z)

def ShortVectors.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ vr : ℝ, HasSpanningBound Em vr → ∀ t : ℝ, 0 < t → t ≤ vr ^ (-(1 / 2 : ℝ)) → ∀ z ∈ D.Xo, D.lam1 z < t →
    1 ≤ D.isoCount t z ∧ D.isoCount t z ≤ (3 * t / D.lam1 z) ^ (2 * D.f * D.j')

def CountScaling.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ θ t : ℝ, 0 < θ → 0 < t →
    D.meanX (D.isoCount (θ * t)) = θ ^ ((2 * D.f * (D.N - 1) : ℕ) : ℝ) * D.meanX (D.isoCount t)

end Statements

namespace Gauss

end Gauss

end GroundTheory.Heights₂.Heights.NineStatements
