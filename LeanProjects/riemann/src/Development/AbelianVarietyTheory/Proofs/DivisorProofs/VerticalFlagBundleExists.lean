import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricFlagsCompatStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest

theorem powerSum_vandermonde_of_regular (HP : Hypotheses2) : (∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsRegSurf q → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (m : ∀ a, Vert.Flag (E a) (r a)) (c : ι → ℝ), (∀ a, VMetric.IsFlagCh2 (H a) (m a) (c a)) → ∀ Φ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ → Φ ((∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = (∏ a, ((r a).factorial : ℝ)) * (2 * ∑ a, c a)) := by
  intro k _ B Y _ _ q p D hB hY π w ι _ E r h H fl hfl m c hc Φ hΦ
  obtain ⟨Ψ, hΨ⟩ := ((HP.p4.arExists k Y p D hY).2 ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a)))
    (Sum.elim (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w))
      (fun z : Σ a, Fin (r a) => (VMetric.grLB (m z.1) z.2 (H z.1)).pull π w))).1
  choose s hs using fun a => (hc a).2
  rw [GlobalTheory.T.flag_bundle_section_lifts_metric HP k B Y q p D hB hY π w ι E r h H fl hfl m (fun a => (hc a).1) Φ hΦ Ψ hΨ,
    GlobalTheory.T.flag_bundle_pullback_metric_flags_compat HP k B Y q p D hB hY π w ι E r h H fl hfl m (fun z => s z.1 z.2) (fun z => (hs z.1).1 z.2) Ψ hΨ]
  have e : 2 * ∑ a, c a = ∑ a, ∑ i, s a i - ∑ a, (h a).flagBc (m a) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hs a).2, ← Finset.sum_div]
    ring
  rw [e, Fintype.sum_sigma]
  ring

theorem powerSum_vandermonde : Hypotheses2 → ArCalc → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar q 1 → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ c : ι → ℝ, (∀ a, (h a).IsCh2Deg (c a)) → ∀ Φ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ → Φ ((∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = (∏ a, ((r a).factorial : ℝ)) * (2 * ∑ a, c a) :=
  fun HP HA HR => GlobalTheory.T.flag_bundle_exists_arithmetic_variety HP HA HR (powerSum_vandermonde_of_regular HP)

end GlobalTheory.CovTest

end
