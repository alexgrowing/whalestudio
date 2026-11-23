import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpan
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_vanishing_sections_span : ∀ {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), L.IsLB → ∀ {k : ℕ} {P : Fin k → X.Modules} {Q K : X.Modules} (f : ∀ i, P i ⟶ Q) (ι : K ⟶ ⨁ P) (w : ι ≫ biproduct.desc f = 0), (ShortComplex.mk ι (biproduct.desc f) w).ShortExact → Subsingleton (GlobalTheory.coh (GlobalTheory.twist K L) 1) → Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map L (f i)).app ⊤)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top | exact GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top <;> assumption)
