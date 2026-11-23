import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricCurvature
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.BlockPoint
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_metric_curvature : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf), Nonempty (Vert.Flag E 2) →
    ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ (j : ℕ) (P : MvPolynomial (Fin 2) ℝ), 1 ≤ j → 2 * j ≤ d + 2 → P.IsHomogeneous (d + 2 - 2 * j) →
        Φ ((X 1 - X 0) ^ (2 * j) * aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) P) =
          oddHarm j * Ψ ((X 1 - X 0) ^ (2 * j - 1) * aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) P) := by
  first | exact @GlobalTheory.BlockPoint.OddTerm.arFun_pow_eq_oddHarm_mul | exact GlobalTheory.BlockPoint.OddTerm.arFun_pow_eq_oddHarm_mul | (intros; apply GlobalTheory.BlockPoint.OddTerm.arFun_pow_eq_oddHarm_mul <;> assumption)
