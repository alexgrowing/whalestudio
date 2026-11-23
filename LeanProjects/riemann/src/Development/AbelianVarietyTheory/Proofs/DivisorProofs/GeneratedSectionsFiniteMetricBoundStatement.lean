import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSectionsFiniteMetricBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_sections_finite_metric_bound : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : Model Y)
    (L : GlobalTheory.HermLB M.p) (k : ℕ+), A.Induced M L k 0 → ∀ (N : ℕ) (s : Fin N → Y.Fn),
    (∀ i, s i ∈ Y.H0 ((k : ℕ) • A.D)) → (∀ x : Y.X, ∃ i, ((k : ℕ) • A.D).GeneratesAt x (s i)) →
    ∃ c : HeightOneSpectrum (𝓞 F) → ℝ, (Function.support c).Finite ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), ∃ j,
        Real.exp (-c v) ≤ e.w (valAt y.1 (s j * (eqn A.D (below y.1) : Y.Fn) ^ (k : ℕ))) *
          Real.exp ((k : ℕ) * A.lg v e y) := by
  first | exact @GlobalTheory.TrueGeo.FinLow.main | exact GlobalTheory.TrueGeo.FinLow.main | (intros; apply GlobalTheory.TrueGeo.FinLow.main <;> assumption)
