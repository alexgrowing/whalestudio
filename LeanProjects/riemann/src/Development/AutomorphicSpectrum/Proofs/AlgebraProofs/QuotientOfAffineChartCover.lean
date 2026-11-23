import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRestrictPreimageOpenStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimageStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCoverStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedChartsStatement

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem exists_iso_of_effectiveEpi {T Y₁ Y₂ : Scheme.{0}} (q₁ : T ⟶ Y₁) (q₂ : T ⟶ Y₂)
    [EffectiveEpi q₁] [EffectiveEpi q₂]
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ T), g₁ ≫ q₁ = g₂ ≫ q₁ ↔ g₁ ≫ q₂ = g₂ ≫ q₂) :
    ∃ e : Y₁ ≅ Y₂, q₁ ≫ e.hom = q₂ := by
  let f : Y₁ ⟶ Y₂ := EffectiveEpi.desc q₁ q₂ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).1 e
  let g : Y₂ ⟶ Y₁ := EffectiveEpi.desc q₂ q₁ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).2 e
  have hf : q₁ ≫ f = q₂ := EffectiveEpi.fac _ _ _
  have hg : q₂ ≫ g = q₁ := EffectiveEpi.fac _ _ _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · rw [← cancel_epi q₁, reassoc_of% hf, hg, Category.comp_id]
  · rw [← cancel_epi q₂, reassoc_of% hg, hf, Category.comp_id]

theorem IsChart.exists_isOpenImmersion {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {V V' : X.Opens}
    {q : V.toScheme ⟶ Y} {q' : V'.toScheme ⟶ Y'} (h : IsChart a b V q) (h' : IsChart a b V' q')
    (hle : V' ≤ V) : ∃ k : Y' ⟶ Y, IsOpenImmersion k ∧ q' ≫ k = X.homOfLE hle ≫ q := by
  obtain ⟨D, rfl⟩ := GlobalTheory.T.invariant_open_chart_preimage h V' hle h'.stable
  obtain ⟨hle₂, q'', hc, hq⟩ := GlobalTheory.T.chart_restrict_preimage_open h D
  have := h'.effectiveEpi
  have := hc.effectiveEpi
  obtain ⟨e, he⟩ := exists_iso_of_effectiveEpi q' q'' fun Z g₁ g₂ ↦ by
    rw [h'.comp_eq_iff, hc.comp_eq_iff]
  refine ⟨e.hom ≫ D.ι, inferInstance, ?_⟩
  rw [reassoc_of% he, hq]

theorem exists_common {P X : Scheme.{0}} {a b : P ⟶ X} {U V : X.Opens}
    (hU : HasAffineChart a b U) (hV : HasAffineChart a b V) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ W, HasAffineChart a b W ∧ x ∈ W ∧ W ≤ U ∧ W ≤ V := by
  obtain ⟨Y, q, hY, hq⟩ := (hasAffineChart_iff a b U).1 hU
  obtain ⟨D, hD⟩ := GlobalTheory.T.invariant_open_chart_preimage hq (U ⊓ V) inf_le_left (by
    have h1 := hq.stable
    have h2 := hV.1
    ext p
    have h1' := SetLike.ext_iff.1 h1 p
    have h2' := SetLike.ext_iff.1 h2 p
    exact and_congr h1' h2')
  have hx : x ∈ U.ι ''ᵁ (q ⁻¹ᵁ D) := hD ▸ ⟨hxU, hxV⟩
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨D', hD', hm, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := q u) (U := D) hu
  obtain ⟨hW, q', hc, hq'⟩ := GlobalTheory.T.chart_restrict_preimage_open hq D'
  have hle' : U.ι ''ᵁ (q ⁻¹ᵁ D') ≤ U ⊓ V := by
    rw [← hD]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hle hv, rfl⟩
  have : IsAffine D'.toScheme := hD'
  exact ⟨_, (hasAffineChart_iff a b _).2 ⟨_, q', this, hc⟩, ⟨u, hm, rfl⟩, hW, hle'.trans inf_le_right⟩

theorem prop_of_charts (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {X Y' : Scheme.{0}} (π : X ⟶ Y') {J : Type} (V : J → X.Opens)
    (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hcomm : ∀ j, (V j).ι ≫ π = q j ≫ em j)
    (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j) (hsurj : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y)
    (hq : ∀ j, Q (q j)) : Q π := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun j ↦ (em j).opensRange) ?_ fun j ↦ ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨j, z, rfl⟩ := hsurj y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, z, rfl⟩
  · refine (Q.arrow_mk_iso_iff (morphismRestrictOpensRange π (em j))).mpr ?_
    have H : IsPullback (q j) (V j).ι (em j) π :=
      IsOpenImmersion.isPullback _ _ _ _ (hcomm j) (by
        rw [Scheme.Opens.opensRange_ι, hpre])
    have e : H.flip.isoPullback.hom ≫ pullback.snd π (em j) = q j := H.flip.isoPullback_hom_snd
    have h' := hq j
    rw [← e] at h'
    exact (Q.cancel_left_of_respectsIso _ _).1 h'

end GlobalTheory.CompanionTheory.FreeQuotGlue

set_option backward.isDefEq.respectTransparency false in

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  intro P X a b h
  let 𝒰 : Set X.Opens := {V | HasAffineChart a b V}
  have hU (U : 𝒰) := (hasAffineChart_iff a b U.1).1 U.2
  choose Y q hY hq using hU
  let R : X → X → Prop := fun x y ↦ ∃ p : P, a p = x ∧ b p = y
  have hk (U V : 𝒰) (h : U.1 ≤ V.1) := (hq V).exists_isOpenImmersion (hq U) h
  choose k hk hqk using hk
  obtain ⟨Y', π, em, hem, hcomm, hpre, hsurj⟩ := GlobalTheory.T.glue_quotient_charts_cover R 𝒰
    (fun U hU V hV x hx hx' ↦ by
      obtain ⟨W, h1, h2, h3, h4⟩ := exists_common hU hV x hx hx'
      exact ⟨W, h1, h2, h3, h4⟩)
    (fun x ↦ by
      obtain ⟨V, h1, h2⟩ := h x
      exact ⟨⟨V, h2⟩, h1⟩)
    Y q (fun U ↦ by have := (hq U).effectiveEpi; infer_instance)
    (fun U ↦ by have := (hq U).surjective; exact Surjective.surj)
    (fun U u v ↦ (hq U).apply_eq_iff u v)
    (fun U x y ⟨p, h1, h2⟩ hx ↦ by
      have : p ∈ a ⁻¹ᵁ U.1 := by change a p ∈ U.1; rwa [h1]
      rw [(hq U).stable] at this
      rw [← h2]; exact this)
    k hk hqk
  refine ⟨Y', π, ?_, ?_, ?_, ?_, ?_⟩
  · exact prop_of_charts (@IsFinite.{0}) π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).isFinite
  · exact prop_of_charts @Flat.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).flat
  · exact prop_of_charts @LocallyOfFinitePresentation.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).lfp
  · exact prop_of_charts @Surjective.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).surjective
  · exact GlobalTheory.T.pullback_of_glued_charts a b π _ Y q em hq hcomm hpre hsurj
