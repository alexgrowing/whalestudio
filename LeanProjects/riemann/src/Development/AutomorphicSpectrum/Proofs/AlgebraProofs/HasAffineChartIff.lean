import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

def IsChart {P X Y : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) (q : V.toScheme ⟶ Y) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
    ∃ a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme,
      a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

theorem hasAffineChart_iff {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) :
    HasAffineChart a b V ↔ ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y), IsAffine Y ∧ IsChart a b V q := by
  constructor
  · rintro ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩
    exact ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
  · rintro ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
    exact ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩

theorem isChart_id (X : Scheme.{0}) : IsChart (𝟙 X) (𝟙 X) ⊤ (⊤ : X.Opens).ι := by
  have : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
  refine ⟨rfl, inferInstance, inferInstance, inferInstance, inferInstance,
    𝟙 X ∣_ ⊤, morphismRestrict_ι _ _, ?_⟩
  exact IsPullback.of_horiz_isIso ⟨rfl⟩

theorem isChart_pullback {X Y : Scheme.{0}} (q : X ⟶ Y) [IsFinite q] [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    IsChart (pullback.fst q q) (pullback.snd q q) ⊤ ((⊤ : X.Opens).ι ≫ q) := by
  have : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
  have hb : IsIso ((pullback.snd q q) ⁻¹ᵁ (⊤ : X.Opens)).ι := (pullback q q).topIso.isIso_hom
  let f := ((pullback.snd q q) ⁻¹ᵁ (⊤ : X.Opens)).ι
  refine ⟨rfl, inferInstance, inferInstance, inferInstance, inferInstance,
    f ≫ pullback.fst q q ≫ inv (⊤ : X.Opens).ι, by simp [f], ?_⟩
  refine IsPullback.of_iso (IsPullback.of_hasPullback q q) (asIso f).symm
    (asIso (⊤ : X.Opens).ι).symm (asIso (⊤ : X.Opens).ι).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [f]
  · rw [← cancel_mono (⊤ : X.Opens).ι]
    simp only [Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      morphismRestrict_ι]
    exact (IsIso.inv_hom_id_assoc f _).symm
  · simp
  · simp

variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}

theorem IsChart.stable (h : IsChart a b V q) : a ⁻¹ᵁ V = b ⁻¹ᵁ V := h.1
theorem IsChart.isFinite (h : IsChart a b V q) : IsFinite q := h.2.1
theorem IsChart.flat (h : IsChart a b V q) : Flat q := h.2.2.1
theorem IsChart.lfp (h : IsChart a b V q) : LocallyOfFinitePresentation q := h.2.2.2.1
theorem IsChart.surjective (h : IsChart a b V q) : Surjective q := h.2.2.2.2.1

theorem IsChart.effectiveEpi (h : IsChart a b V q) : EffectiveEpi q := by
  have := h.isFinite; have := h.flat; have := h.surjective
  infer_instance

theorem IsChart.comp_eq_iff (h : IsChart a b V q) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ V.toScheme) :
    g₁ ≫ q = g₂ ≫ q ↔ ∃ l : Z ⟶ P, l ≫ a = g₁ ≫ V.ι ∧ l ≫ b = g₂ ≫ V.ι := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := h
  constructor
  · intro e
    refine ⟨hp.lift g₁ g₂ e ≫ (b ⁻¹ᵁ V).ι, ?_, ?_⟩
    · rw [Category.assoc, ← ha, hp.lift_fst_assoc]
    · rw [Category.assoc, ← morphismRestrict_ι, hp.lift_snd_assoc]
  · rintro ⟨l, h1, h2⟩
    have hr : Set.range l ⊆ Set.range (b ⁻¹ᵁ V).ι := by
      rintro _ ⟨z, rfl⟩
      have : b (l z) ∈ V := by
        have : b (l z) = V.ι (g₂ z) := congr($h2 z)
        rw [this]; exact (g₂ z).2
      simpa using this
    let l' : Z ⟶ (b ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ l hr
    have hl : l' ≫ (b ⁻¹ᵁ V).ι = l := IsOpenImmersion.lift_fac _ _ _
    have e1 : l' ≫ a' = g₁ := by
      rw [← cancel_mono V.ι, Category.assoc, ha, reassoc_of% hl, h1]
    have e2 : l' ≫ (b ∣_ V) = g₂ := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hl, h2]
    rw [← e1, ← e2, Category.assoc, Category.assoc, hp.w]

theorem IsChart.apply_eq_iff (h : IsChart a b V q) (u v : V.toScheme) :
    q u = q v ↔ ∃ p : P, a p = V.ι u ∧ b p = V.ι v := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := id h
  constructor
  · intro e
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback u v e
    let p : (b ⁻¹ᵁ V).toScheme := hp.isoPullback.inv z
    have e1 : a' p = u := by
      rw [← h1]
      exact congr($(hp.isoPullback_inv_fst) z)
    have e2 : (b ∣_ V) p = v := by
      rw [← h2]
      exact congr($(hp.isoPullback_inv_snd) z)
    refine ⟨(b ⁻¹ᵁ V).ι p, ?_, ?_⟩
    · rw [← e1]; exact (congr($ha p)).symm
    · rw [← e2]; exact (congr($(morphismRestrict_ι b V) p)).symm
  · rintro ⟨p, h1, h2⟩
    have hp' : p ∈ b ⁻¹ᵁ V := by
      change b p ∈ V
      rw [h2]; exact v.2
    let p' : (b ⁻¹ᵁ V).toScheme := ⟨p, hp'⟩
    have hi : (b ⁻¹ᵁ V).ι p' = p := rfl
    have e1 : a' p' = u := V.ι.isOpenEmbedding.injective (by
      rw [← h1, ← hi]; exact congr($ha p'))
    have e2 : (b ∣_ V) p' = v := V.ι.isOpenEmbedding.injective (by
      rw [← h2, ← hi]; exact congr($(morphismRestrict_ι b V) p'))
    rw [← e1, ← e2]
    exact congr($(hp.w) p')

end GlobalTheory.CompanionTheory.FreeQuotGlue
