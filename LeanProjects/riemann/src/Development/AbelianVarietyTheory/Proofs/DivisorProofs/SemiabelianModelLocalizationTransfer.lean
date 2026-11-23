import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueTwo
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdFib.Glue

theorem exists_lift {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S''} [GrpObj A] (f : S' ⟶ S)
    (k : S'' ⟶ S') {j : S'' ⟶ S} (e : k ≫ f = j) {θ : A.left ⟶ G.left} (h : IsGrpPullback A G j θ) :
    ∃ θ' : A.left ⟶ ((Over.pullback f).obj G).left, IsGrpPullback A ((Over.pullback f).obj G) k θ' ∧
      θ' ≫ pullback.fst G.hom f = θ := by
  subst e
  let θ' : A.left ⟶ pullback G.hom f := pullback.lift θ (A.hom ≫ k) (by rw [Category.assoc, h.1.w])
  have e' : θ' ≫ pullback.fst G.hom f = θ := pullback.lift_fst _ _ _
  exact ⟨θ', (isGrpPullback_pullback G f).cancel (h.congr rfl e'.symm) (pullback.lift_snd _ _ _), e'⟩

theorem intAct_comm {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℤ) :
    ((ExtUnique.intAct G').act n).left ≫ φ = φ ≫ ((ExtUnique.intAct G).act n).left := by
  have e₁ := map_zpow (pushHom h G') (𝟙 G') n
  have e₂ := GrpObj.comp_zpow (pushHom h G' (𝟙 G')) (𝟙 G) n
  rw [Category.comp_id, ← e₁] at e₂
  have e₃ := congrArg (fun z => z.left) e₂
  refine e₃.symm.trans ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]
  rfl

theorem exists_glue_opens (h : GlobalTheory.Published.SemiAbelianHomExtension) {X : Scheme.{0}} [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) {K : Type} [Field K]
    (j : Sp K ⟶ X) [IsPreimmersion j] (hj : IsGenericPointHom j) {A : Over (Sp K)} [GrpObj A] (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) {G₁ : Over U.toScheme} [GrpObj G₁] {G₂ : Over V.toScheme} [GrpObj G₂]
    (s₁ : IsSemiAbelian G₁) (s₂ : IsSemiAbelian G₂) {k₁ : Sp K ⟶ U} {k₂ : Sp K ⟶ V} (e₁ : k₁ ≫ U.ι = j)
    (e₂ : k₂ ≫ V.ι = j) {θ₁ : A.left ⟶ G₁.left} {θ₂ : A.left ⟶ G₂.left} (h₁ : IsGrpPullback A G₁ k₁ θ₁)
    (h₂ : IsGrpPullback A G₂ k₂ θ₂) :
    ∃ (G : Over X) (_ : GrpObj G) (θ : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j θ := by
  obtain ⟨w, w₁, w₂⟩ := GroupGlue.exists_inf k₁ k₂ (e₁.trans e₂.symm)
  have hw : w ≫ (U ⊓ V).ι = j := by
    rw [← e₁, ← w₁, Category.assoc, Scheme.homOfLE_ι]
  have : Nonempty (U ⊓ V).toScheme := ⟨w (IsLocalRing.closedPoint K)⟩
  have : IsIntegral (U ⊓ V).toScheme := isIntegral_of_isOpenImmersion (U ⊓ V).ι
  have : IsLocallyNoetherian (U ⊓ V).toScheme := isLocallyNoetherian_of_isOpenImmersion (U ⊓ V).ι
  have : CompactSpace (U ⊓ V).toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact ((U ⊓ V : X.Opens) : Set X))
  have : AlgebraicGeometry.IsNoetherian (U ⊓ V).toScheme := {}
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : GlobalTheory.IsNormalScheme (U ⊓ V).toScheme := GlobalTheory.IsNormalScheme.of_isOpenImmersion (U ⊓ V).ι
  obtain ⟨_, _⟩ := IsGenericPointHom.quasiCompact_and_dominant_of_comp (k := w) (i := (U ⊓ V).ι) (hw ▸ hj)
  have : IsPreimmersion (w ≫ (U ⊓ V).ι) := hw ▸ inferInstance
  have : IsPreimmersion w := IsPreimmersion.of_comp w (U ⊓ V).ι
  have hgw : IsGenericPointHom w := IsGenericPointHom.of_isPreimmersion w
  obtain ⟨t₁, p₁, -⟩ := exists_lift (X.homOfLE inf_le_left) w w₁ h₁
  obtain ⟨t₂, p₂, -⟩ := exists_lift (X.homOfLE inf_le_right) w w₂ h₂
  have r₁ := IsSemiAbelian.pullback (f := X.homOfLE (inf_le_left : U ⊓ V ≤ U)) G₁ s₁
  have r₂ := IsSemiAbelian.pullback (f := X.homOfLE (inf_le_right : U ⊓ V ≤ V)) G₂ s₂
  obtain ⟨E, ⟨_, -⟩, -⟩ := h.generic_existsUnique_iso_of_extensions (GlobalTheory.IsNormalScheme.pred _) hgw r₁ r₂ p₁ p₂
  have q₁ := isGrpPullback_pullback G₁ (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
  have q₂ := ((isGrpPullback_of_iso E).comp
    (isGrpPullback_pullback G₂ (X.homOfLE (inf_le_right : U ⊓ V ≤ V)))).congr (Category.id_comp _) rfl
  have := s₁.comm
  have := s₂.comm
  have := r₁.comm
  obtain ⟨G, _, -, ψ₁, ψ₂, hG, g₁, -⟩ := GroupGlue.exists_glue_two ℤ X U V G₁ G₂ _ (ExtUnique.intAct G₁)
    (ExtUnique.intAct G₂) (ExtUnique.intAct _) _ _ hUV s₁ s₂ q₁ q₂ fun n => ⟨intAct_comm q₁ n, intAct_comm q₂ n⟩
  exact ⟨G, inferInstance, _, hG, (h₁.comp g₁).congr e₁ rfl⟩

theorem exists_transport {X Y T : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] {A : Over T} [GrpObj A] {G : Over Y}
    [GrpObj G] (s : IsSemiAbelian G) {k : T ⟶ Y} {θ : A.left ⟶ G.left} (h : IsGrpPullback A G k θ) :
    ∃ (G' : Over f.opensRange.toScheme) (_ : GrpObj G') (k' : T ⟶ f.opensRange) (θ' : A.left ⟶ G'.left),
      IsSemiAbelian G' ∧ k' ≫ f.opensRange.ι = k ≫ f ∧ IsGrpPullback A G' k' θ' := by
  obtain ⟨θ', p, -⟩ := exists_lift f.isoOpensRange.inv (k ≫ f.isoOpensRange.hom) (by simp) h
  exact ⟨_, _, _, θ', IsSemiAbelian.pullback _ G s, by simp, p⟩

theorem hasModel_of_coprime : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (K : Type) [Field K] [NumberField K] (A : Over (Sp K)) [GrpObj A] (a b : 𝓞 K), a ≠ 0 → b ≠ 0 → IsCoprime a b → (∃ (G : Over (Sp (Localization.Away (a : 𝓞 K)))) (_ : GrpObj G) (θ : A.left ⟶ G.left) (i : Localization.Away (a : 𝓞 K) →+* K), IsSemiAbelian G ∧ i.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K ∧ IsGrpPullback A G (spMap i) θ) → (∃ (G : Over (Sp (Localization.Away (b : 𝓞 K)))) (_ : GrpObj G) (θ : A.left ⟶ G.left) (i : Localization.Away (b : 𝓞 K) →+* K), IsSemiAbelian G ∧ i.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K ∧ IsGrpPullback A G (spMap i) θ) → HasModel A := by
  rintro h K _ _ A _ a b - - hab ⟨G₁, _, θ₁, i₁, s₁, c₁, h₁⟩ ⟨G₂, _, θ₂, i₂, s₂, c₂, h₂⟩
  have o₁ : IsOpenImmersion (spMap (algebraMap (𝓞 K) (Localization.Away a))) := IsOpenImmersion.of_isLocalization a
  have o₂ : IsOpenImmersion (spMap (algebraMap (𝓞 K) (Localization.Away b))) := IsOpenImmersion.of_isLocalization b
  obtain ⟨H₁, _, k₁, t₁, r₁, e₁, p₁⟩ := exists_transport (spMap (algebraMap (𝓞 K) (Localization.Away a))) s₁ h₁
  obtain ⟨H₂, _, k₂, t₂, r₂, e₂, p₂⟩ := exists_transport (spMap (algebraMap (𝓞 K) (Localization.Away b))) s₂ h₂
  have : IsPreimmersion (spMap (algebraMap (𝓞 K) K)) := IsPreimmersion.of_isLocalization (S := K) (nonZeroDivisors (𝓞 K))
  refine exists_glue_opens h (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec (𝓞 K)) _
    (IsGenericPointHom.fractionField (𝓞 K) K) _ _ ?_ r₁ r₂ (e₁.trans ?_) (e₂.trans ?_) p₁ p₂
  · refine top_le_iff.1 fun x _ => ?_
    have key : ∀ c : 𝓞 K, c ∉ x.asIdeal →
        x ∈ Set.range (PrimeSpectrum.comap (algebraMap (𝓞 K) (Localization.Away c))) := fun c hc => by
      rw [PrimeSpectrum.localization_away_comap_range _ c]
      exact hc
    by_cases ha : a ∈ x.asIdeal
    · refine Or.inr (key b fun hb => x.isPrime.ne_top ?_)
      obtain ⟨u, v, huv⟩ := hab
      rw [Ideal.eq_top_iff_one, ← huv]
      exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · exact Or.inl (key a ha)
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, c₁]
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, c₂]

end GlobalTheory.BdFib.Glue

end
