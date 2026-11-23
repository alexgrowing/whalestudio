import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_torsion_approximation : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ →
    ∀ (θ : B →+* C), (∀ s ∈ S, ‖θ s‖ ≤ 1) → θ ϖ ≠ 0 → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q → ‖(q : C)‖ ≤ ‖θ ϖ‖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → ∀ (w : ℕ → C), w 0 = 0 → (∀ n, w (n + 1) ^ q + θ ϖ * w (n + 1) = w n) →
      (∀ n, ‖θ (v n) - w n‖ ≤ ‖θ ϖ‖) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) → θ Q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion | exact GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion | (intros; apply GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion <;> assumption)
