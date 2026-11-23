import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivatives
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_automorphic_derivatives : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ F, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → ∃ ψ, Repr V μ 𝓕 F ψ ∧ IsAutFun V ψ ∧ (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧ ∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) ∧ Repr V μ 𝓕 (l.foldr (dL2 θ V ρ) F) (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) := by
  first | exact @GlobalTheory.SmoothRep.exists_smooth_repr | exact GlobalTheory.SmoothRep.exists_smooth_repr | (intros; apply GlobalTheory.SmoothRep.exists_smooth_repr <;> assumption)
