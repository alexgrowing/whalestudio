import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricFlagsCompat
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_metric_flags_compat : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsRegSurf q → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (m : ∀ a, Vert.Flag (E a) (r a)) (s : (Σ a, Fin (r a)) → ℝ), (∀ z, (VMetric.grLB (m z.1) z.2 (H z.1)).IsSelfInter (s z)) → ∀ Ψ : MvPolynomial ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ℝ →ₗ[ℝ] ℝ, IsArFun (Sum.elim (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) (fun z : Σ a, Fin (r a) => (VMetric.grLB (m z.1) z.2 (H z.1)).pull π w)) D Ψ → Ψ (rename Sum.inr (∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * rename Sum.inl (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = (∏ a, ((r a).factorial : ℝ)) * ∑ z, s z := by
  first | exact @GlobalTheory.FlagPullSquare.powerSum_pull_vandermonde | exact GlobalTheory.FlagPullSquare.powerSum_pull_vandermonde | (intros; apply GlobalTheory.FlagPullSquare.powerSum_pull_vandermonde <;> assumption)
