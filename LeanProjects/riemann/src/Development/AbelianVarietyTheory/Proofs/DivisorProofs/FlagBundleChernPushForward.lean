import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricFlagsCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCoverGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.VdmProj

theorem residueDegree_fst_eq {B B₁ Y : Scheme.{0}} [IsIntegral B₁] (π : Y ⟶ B) (g : B₁ ⟶ B)
    [IsIntegral (Limits.pullback π g)] (hs : Function.Surjective (Limits.pullback.snd π g))
    (hg : g.residueDegree (genericPoint B₁) ≠ 0) :
    (Limits.pullback.fst π g).residueDegree (genericPoint (Limits.pullback π g : Scheme.{0})) =
      g.residueDegree (genericPoint B₁) := by
  obtain ⟨z, hz⟩ := hs (genericPoint B₁)
  have h₂ : Limits.pullback.snd π g (genericPoint (Limits.pullback π g : Scheme.{0})) = genericPoint B₁ :=
    GenericBaseChange.eq_genericPoint_of_specializes
      (hz ▸ (genericPoint_specializes z).map (Limits.pullback.snd π g).continuous)
  have hF := GlobalTheory.T.generic_point_pullback_residue_field GlobalTheory.T.isField_of_unique_prime_stalk π g (GlobalTheory.T.spec_tensor_preimmersion _ _ _) (h₂ ▸ hg)
  rw [GlobalTheory.T.residue_degree_fst_eq_finrank π g _ hF, GlobalTheory.T.finrank_tensor_residue_degree]
  change g.residueDegree (Limits.pullback.snd π g (genericPoint _)) = _
  rw [h₂]

theorem vdm_mul_pull_of_regular (HP : Hypotheses2) {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] [IsIntegral Y]
    {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {e D : ℕ} (hq : IsArithVar q e) (hreg : ∀ b : B, IsRegularLocalRing (B.presheaf.stalk b))
    (hp : IsArithVar p D) (π : Y ⟶ B) (w : π ≫ q = p) {ι : Type} [Fintype ι] {E : ι → B.Modules} {r : ι → ℕ}
    {h : ∀ a, VMetric q (E a) (r a)} (H : ∀ a, (h a).IsCInf)
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hfl : IsFlagBundle π E r fl)
    {κ μ : Type} [Fintype κ] [Fintype μ] {L : κ → HermLB p} {A : μ → HermLB q} (x : (Σ a, Fin (r a)) → κ) (y : μ → κ)
    (hx : ∀ z, (L (x z)).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)))
    (hy : ∀ m, (L (y m)).Isometric ((A m).pull π w)) {Φ : MvPolynomial μ ℝ →ₗ[ℝ] ℝ} {Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun A e Φ) (hΨ : IsArFun L D Ψ) {P : MvPolynomial μ ℝ} (hP : P.IsHomogeneous (e + 1)) :
    Ψ (rename x (vdm r) * rename y P) = (∏ a, ((r a).factorial : ℝ)) * Φ P := by
  have hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a) := fun a => (h a).isVB
  have hD : D - e = ∑ a, r a * (r a - 1) / 2 := by
    have := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hfl
    have := hq.isLocallyNoetherian
    have h₁ := (GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective B Y π (∑ a, r a * (r a - 1) / 2) e
      (GlobalTheory.FlagSurj.isFlagBundle_surjective B Y π ι E r fl hE hfl) hq.dim_eq).symm.trans hp.dim_eq
    have h₂ : e + (∑ a, r a * (r a - 1) / 2) + 1 = D + 1 := by exact_mod_cast h₁
    omega
  obtain ⟨Ψ', hΨ'⟩ := ((HP.p4.arExists k Y _ _ hp).2 _ (Sum.elim
    (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) fun a => (A a).pull π w)).1
  have key := GlobalTheory.T.flag_bundle_metric_setup HP k B Y q p e D hq hreg hp π w ι E r h H fl hfl μ A Φ Ψ' hΦ hΨ' P _ _ hP
    (hD ▸ FlagPullSquare.isHomogeneous_rootDiscr r) (FlagPullSquare.antisymm_rootDiscr r)
  have e₁ := apply_aeval HP.p4.arIso hp hΨ hΨ' (Sum.elim (fun z => MvPolynomial.X (x z)) fun m => MvPolynomial.X (y m)) (by
    rintro (z | m)
    · exact ⟨Pi.single (x z) 1, by simp [lin, Pi.single_apply, apply_ite], by
        simpa [Pi.single_apply] using HermLB.icls_eq_iff.2 (hx z)⟩
    · exact ⟨Pi.single (y m) 1, by simp [lin, Pi.single_apply, apply_ite], by
        simpa [Pi.single_apply] using HermLB.icls_eq_iff.2 (hy m)⟩)
    (rename Sum.inl (GoodMetric.rootDiscr r) * rename Sum.inr P)
  rw [← key, ← e₁, vdm, FlagPullSquare.prod_Ioi_eq_rootDiscr]
  congr 1
  rw [map_mul, aeval_rename, aeval_rename, rename_eq_aeval, rename_eq_aeval]
  rfl

theorem vdm_mul_pull : Hypotheses2 → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (e D : ℕ), IsArithVar q e → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (κ μ : Type) [Fintype κ] [Fintype μ] (L : κ → HermLB p) (A : μ → HermLB q) (x : (Σ a, Fin (r a)) → κ) (y : μ → κ), (∀ z, (L (x z)).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w))) → (∀ m, (L (y m)).Isometric ((A m).pull π w)) → ∀ (Φ : MvPolynomial μ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), IsArFun A e Φ → IsArFun L D Ψ → ∀ P : MvPolynomial μ ℝ, P.IsHomogeneous (e + 1) → Ψ (rename x (vdm r) * rename y P) = (∏ a, ((r a).factorial : ℝ)) * Φ P := by
  intro HP hR k _ B Y _ _ q p e D hq hp π w ι _ E r h H fl hfl κ μ _ _ L A x y hx hy Φ Ψ hΦ hΨ P hP
  subst w
  have hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a) := fun a => (h a).isVB
  obtain ⟨B₁, _, g, a₁, hreg, a₃, a₄⟩ := AlterationOrder.regularAlteration_order hR k B q e hq
  obtain ⟨_, hf⟩ := Gen.isCov_pullback_fst hq hp ⟨a₁, a₃, a₄⟩ hE hfl
  have hfl' := FlagBaseChange.isFlagBundle_pullFlag B Y B₁ π g ι E r fl hfl
  have w₁ : Limits.pullback.fst π g ≫ π ≫ q = Limits.pullback.snd π g ≫ g ≫ q := Limits.pullback.condition_assoc q
  have hdeg := residueDegree_fst_eq π g
    (GlobalTheory.FlagSurj.isFlagBundle_surjective _ _ _ ι _ r _ (fun a => (hE a).pullback g) hfl') a₄
  have hΦ₁ := (HP.p4.arProj k B B₁ q _ _ hq a₁ g rfl a₃ a₄).2 _ _ Φ hΦ
  have hΨ₁ := (HP.p4.arProj k Y _ _ _ _ hp (w₁ ▸ hf.1) _ w₁ hf.2.1 hf.2.2).2 _ _ Ψ hΨ
  have key := vdm_mul_pull_of_regular HP a₁ hreg (w₁ ▸ hf.1) (Limits.pullback.snd π g) rfl
    (fun a => (H a).pull g rfl) hfl' x y
    (fun z => ((hx z).pull _ w₁).trans (Gen.isometric_grLB_pull_ofIso _ _ w₁
      (Gen.isIsometry_sqIso Limits.pullback.condition (h z.1) rfl rfl w₁ rfl) (fl z.1) z.2))
    (fun m => ((hy m).pull _ w₁).trans (Gen.isometric_sq Limits.pullback.condition (A m) rfl rfl w₁ rfl))
    hΦ₁ hΨ₁ hP
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hdeg, smul_eq_mul, smul_eq_mul, mul_left_comm] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 a₄) key

end GlobalTheory.VdmProj
