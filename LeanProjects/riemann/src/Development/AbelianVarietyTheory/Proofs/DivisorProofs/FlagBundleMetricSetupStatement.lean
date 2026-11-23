import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open MvPolynomial GlobalTheory.CovTop GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_metric_setup : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), IsArithVar q d → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (κ : Type) [Fintype κ] (A : κ → HermLB q) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial ((Σ a, Fin (r a)) ⊕ κ) ℝ →ₗ[ℝ] ℝ), IsArFun A d Φ → IsArFun (Sum.elim (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) fun a => (A a).pull π w) D Ψ → ∀ (P : MvPolynomial κ ℝ) (Q : MvPolynomial (Σ a, Fin (r a)) ℝ) (c : ℝ), P.IsHomogeneous (d + 1) → Q.IsHomogeneous (D - d) → GlobalTheory.GoodMetric.antisymm Q = c • GlobalTheory.GoodMetric.rootDiscr r → Ψ (rename Sum.inl Q * rename Sum.inr P) = c * Φ P := by
  first | exact @GlobalTheory.FibreProj.flag_mul_pull | exact GlobalTheory.FibreProj.flag_mul_pull | (intros; apply GlobalTheory.FibreProj.flag_mul_pull <;> assumption)
