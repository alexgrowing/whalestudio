import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianMetricGrading
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_metric_grading : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp k) (d₁ : ℕ) (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) (E₁ : Y₁.Modules) (h₁ : VMetric q₁ E₁ 2)
      (H₁ : h₁.IsCInf) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (M : (Σ a, Fin (r a)) → HermLB q₁),
      D = d₁ + 1 ∧ IsArithVar q₁ d₁ ∧ IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i ((H a).pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i' ((H a).pull π w)) ∧
      ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        ((M z).pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := by
  first | exact @GlobalTheory.SwapBundle.swapFl_bundle | exact GlobalTheory.SwapBundle.swapFl_bundle | (intros; apply GlobalTheory.SwapBundle.swapFl_bundle <;> assumption)
