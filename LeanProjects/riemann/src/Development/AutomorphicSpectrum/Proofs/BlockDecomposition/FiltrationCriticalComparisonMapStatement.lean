import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_critical_comparison_map : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {d : ℕ} (E : Frame Φ (d + 1))
    (a b : ℤ → IdF Φ.A) (r : ℤ), (∀ r' T, (b r').S T ≤ (a r').S T) → Q.Crit a r → Q.Crit a (r - 1) → Q.Crit b r → Q.Crit b (r - 1) →
    ∃ β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)),
      (∀ X, Function.Injective ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom) ∧
      (∀ X, Function.Exact ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom (β.app X).hom) ∧
      (∀ X, Function.Surjective (β.app X).hom) ∧
      ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z' := by
  first | exact @GlobalTheory.CompanionTheory.PolySes.ses | exact GlobalTheory.CompanionTheory.PolySes.ses | (intros; apply GlobalTheory.CompanionTheory.PolySes.ses <;> assumption)
