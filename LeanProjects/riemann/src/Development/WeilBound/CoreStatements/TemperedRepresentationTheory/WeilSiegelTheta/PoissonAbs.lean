import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.BC

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions

variable {D : D7}

def fhat (ψ : AddChar (AF D.host.F) ℂ) {r : ℕ} (lam : Measure (hermA D r)) (f : hermA D r → ℂ) (β : ratHerm D r) : ℂ :=
  ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul β.1.1 b.1 : Mx D r r))) ∂lam

def PoissonAbs : Prop :=
  ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 →
  ∀ f : hermA D r → ℂ, Continuous f → Integrable f lam →
    (∀ K : Set (hermA D r), IsCompact K → ∃ g : ratHerm D r → ℝ, Summable g ∧ ∀ γ : ratHerm D r, ∀ x ∈ K, ‖f (x + γ.1)‖ ≤ g γ) →
    Summable (fun β : ratHerm D r => fhat ψ lam f β) →
    HasSum (fun β : ratHerm D r => fhat ψ lam f β) (∑' γ : ratHerm D r, f γ.1)

def JtCont : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ → Continuous (Jt ψ V μ φ)

def JtInt : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ → Integrable (Jt ψ V μ φ) lam

def JtPer : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
  ∀ K : Set (hermA D r), IsCompact K → ∃ g : ratHerm D r → ℝ, Summable g ∧
    ∀ γ : ratHerm D r, ∀ x ∈ K, ‖Jt ψ V μ φ (x + γ.1)‖ ≤ g γ

def WSum : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    Summable (fun β : HermE D r => ‖W ψ V μ lam φ β‖)

end PositivityTheory.GramSchwartzFunctions.BC
