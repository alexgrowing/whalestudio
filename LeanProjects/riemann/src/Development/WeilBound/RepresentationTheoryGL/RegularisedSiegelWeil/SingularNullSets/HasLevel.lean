import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw

def HasLevel {D : D7} {n : ℕ} {X : Type} (f : G D n → X) : Prop :=
  ∃ U : Subgroup (G D n), IsOpen (U : Set (G D n)) ∧ ∀ k ∈ U, k ∈ finPts D.sp.cm.sig (Jst D n) → ∀ g, f (g * k) = f g

def ResCore : Prop :=
  ∀ (D : D7) (n t : ℕ) (B W : HSp D), Nonempty (HypDec B W t) → W.rank + t = n → W.rank + 2 < 2 * t → W.rank < t →
  1 ≤ W.rank → ∀ ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ W.rank → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μB : Measure (Mx D B.rank n)) (μW : Measure (Mx D W.rank n)), (∃ 𝓕, IsCovolOne (ratMx D B.rank n) μB 𝓕) →
    (∃ 𝓕, IsCovolOne (ratMx D W.rank n) μW 𝓕) →
  ∀ (ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)) (ωW : G D n →* Module.End ℂ (schwartzA θ W.rank n)),
    IsWeilSch ψ χ θ B μB ωB → IsWeilSch ψ χ θ W μW ωW →
  ∀ H : G D n → ℝ≥0, IsHt H → HasLevel H → ∀ Φ : schwartzA θ B.rank n,
  ∀ U d E σ, IsCont H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) U d E σ → ∀ ε, IsRad U d ((t : ℂ) / 2) ε →
    (∀ k, 2 ≤ k → cf d E ((t : ℂ) / 2) ε k = 0) ∧
    ∀ (X : Type) [MeasurableSpace X] (π : Measure X) [IsFiniteMeasure π] (c : X → G D n) (κ : X → ℂ), Measurable c →
      IsCompact (closure (Set.range c)) → Integrable κ π →
      (∀ (Ψ : schwartzA θ W.rank n) (h : GA D W), ∫ x, theta ωW Ψ (c x) h * κ x ∂π = 0) →
      ∫ x, cf d E ((t : ℂ) / 2) ε 1 (c x) * κ x ∂π = 0

end PositivityTheory.Rg.Rsw

end
