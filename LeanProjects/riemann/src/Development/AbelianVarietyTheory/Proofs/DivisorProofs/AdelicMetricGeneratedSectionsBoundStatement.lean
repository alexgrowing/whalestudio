import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricGeneratedSectionsBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_metric_generated_sections_bound : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (k : ℕ+) (x : Y.X),
    IsClosed ({x} : Set Y.X) →
    (∀ y : AlgPt Y, below y.1 = x → {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, A.lg v e y ≠ 0}.Finite) →
    ∀ s : Y.Fn, ((k : ℕ) • A.D).GeneratesAt x s →
    ∀ (α : (F →+* ℂ) → ℝ) (β : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support β).Finite →
    (∀ (σ : F →+* ℂ) (z : Pts Y σ), under z = x →
      Real.exp (-(2 * α σ)) ≤ C.pn Y σ _ (C.mPow Y σ A.D (k : ℕ) (A.m σ)) (C.cx Y σ s) z) →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), below y.1 = x →
      Real.exp (-β v) ≤ e.w (valAt y.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))) * Real.exp ((k : ℕ) * A.lg v e y)) →
    A.ht x ≤ (∑ σ : F →+* ℂ, (α σ + (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) + ∑ᶠ v, β v) /
      ((k : ℕ) * (A.n : ℕ) * (Module.finrank ℚ F : ℝ)) := by
  first | exact @GlobalTheory.TrueGeo.HtEvalUp.main | exact GlobalTheory.TrueGeo.HtEvalUp.main | (intros; apply GlobalTheory.TrueGeo.HtEvalUp.main <;> assumption)
