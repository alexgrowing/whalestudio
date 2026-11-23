import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoversCommonRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackCoverIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCoverGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometricAltBis
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagReduce

theorem exists_common_flagCover (hR : RegularAlteration) {k : Type} [CommRing k] {B : Scheme.{0}} [IsIntegral B]
    {q : B ⟶ Sp k} (hB : IsArithVar q 1) {ι : Type} [Fintype ι] {E : ι → B.Modules} {r : ι → ℕ}
    {h : ∀ a, VMetric q (E a) (r a)} (H : ∀ a, (h a).IsCInf) {c : ι → ℝ} (hc : ∀ a, (h a).IsCh2Deg (c a)) :
    ∃ (C : RegCover q) (m : ∀ a, Vert.Flag ((Scheme.Modules.pullback C.ρ).obj (E a)) (r a)),
      ∀ a, VMetric.IsFlagCh2 ((H a).pull C.ρ rfl) (m a) (C.deg * c a) := by
  let M : ∀ a, (h a).FlagModel := fun a => (hc a).1.some
  have key : ∀ s : Finset ι, ∃ C : RegCover q, ∀ a ∈ s, ∃ t : C.Y ⟶ (M a).Y, t ≫ (M a).ρ = C.ρ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨(GlobalTheory.T.exists_regular_cover_of_alteration hR k B q hB).some, fun a ha => by simp at ha⟩
    | insert a s ha ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨C', ⟨t₁, e₁⟩, t₂, e₂⟩ := GlobalTheory.T.regular_covers_common_refinement hR k B q hB C (M a).toRegCover
      refine ⟨C', fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact ⟨t₂, e₂⟩
      · obtain ⟨t, ht⟩ := hC b hb
        exact ⟨t₁ ≫ t, by rw [Category.assoc, ht, e₁]⟩
  obtain ⟨C, hC⟩ := key Finset.univ
  choose t ht using fun a => hC a (Finset.mem_univ a)
  exact ⟨C, fun a => ((M a).flag.pull (t a)).ofIso
    ((Scheme.Modules.pullbackComp (t a) (M a).ρ).app (E a) ≪≫ (Scheme.Modules.pullbackCongr (ht a)).app (E a)),
    fun a => (hc a).2 ⟨C, (H a).pull C.ρ rfl, _⟩⟩

theorem powerSum_vandermonde_reduce : Hypotheses2 → ArCalc → RegularAlteration → (∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsRegSurf q → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (m : ∀ a, Vert.Flag (E a) (r a)) (c : ι → ℝ), (∀ a, VMetric.IsFlagCh2 (H a) (m a) (c a)) → ∀ Φ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ → Φ ((∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = (∏ a, ((r a).factorial : ℝ)) * (2 * ∑ a, c a)) → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar q 1 → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ c : ι → ℝ, (∀ a, (h a).IsCh2Deg (c a)) → ∀ Φ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ → Φ ((∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = (∏ a, ((r a).factorial : ℝ)) * (2 * ∑ a, c a) := by
  intro _ hA hR hyp k _ B Y _ _ q p D hB hY π w ι _ E r h H fl hfl c hc Φ hΦ
  obtain ⟨C, m, hm⟩ := exists_common_flagCover hR hB H hc
  obtain ⟨hI, hY', hdom⟩ := GlobalTheory.T.flag_bundle_pullback_cover_integral k B Y q p D hB hY π w ι E r (fun a => (h a).isVB) fl hfl C
  haveI := hI
  obtain ⟨hgen, hdeg⟩ := GlobalTheory.T.pullback_cover_generic_point k B Y q π hB hdom C
  have w' : Limits.pullback.snd π C.ρ ≫ C.ρ ≫ q = Limits.pullback.fst π C.ρ ≫ p := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, w]
  have hproj := (hA.arProj k Y (Limits.pullback π C.ρ) p (Limits.pullback.fst π C.ρ ≫ p) D hY hY'
    (Limits.pullback.fst π C.ρ) rfl hgen (by rw [hdeg]; exact C.finite)).2 (Σ a, Fin (r a)) _ Φ hΦ
  have hiso := ((hA.arIso k (Limits.pullback π C.ρ) (Limits.pullback.fst π C.ρ ≫ p) D hY').2 _ _ _ hproj).2.1
    (fun z => VMetric.grLB (FlagBaseChange.pullFlag π C.ρ (fl z.1)) z.2
      (((H z.1).pull C.ρ rfl).pull (Limits.pullback.snd π C.ρ) w'))
    (fun z => GlobalTheory.T.grLB_pull_isometric_pullFlag k B Y C.Y q p π w C.ρ (E z.1) (r z.1) (h z.1) (H z.1) (fl z.1) w' z.2)
  have e := hyp k C.Y (Limits.pullback π C.ρ) (C.ρ ≫ q) (Limits.pullback.fst π C.ρ ≫ p) D C.reg hY'
    (Limits.pullback.snd π C.ρ) w' ι (fun a => (Scheme.Modules.pullback C.ρ).obj (E a)) r
    (fun a => (h a).pull C.ρ rfl) (fun a => (H a).pull C.ρ rfl) (fun a => FlagBaseChange.pullFlag π C.ρ (fl a))
    (GlobalTheory.T.flag_bundle_base_change B Y C.Y π ι E r fl hfl C.ρ) m (fun a => C.deg * c a) hm _ hiso
  rw [hdeg, LinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum] at e
  have hd : (C.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 C.deg_pos.ne'
  apply mul_left_cancel₀ hd
  rw [e]
  ring

end GlobalTheory.FlagReduce
