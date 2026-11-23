import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem isPullback_of_preimage_opensRange {X Y Y' : Scheme.{0}} (π : X ⟶ Y') (V : X.Opens)
    (q : V.toScheme ⟶ Y) (em : Y ⟶ Y') [IsOpenImmersion em] (hc : V.ι ≫ π = q ≫ em)
    (hpre : π ⁻¹ᵁ em.opensRange = V) : IsPullback q V.ι em π :=
  IsOpenImmersion.isPullback q V.ι em π hc (by rw [hpre, Scheme.Opens.opensRange_ι])

theorem IsChart.isIso_restrict_lift {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {π : X ⟶ Y'} {V : X.Opens}
    {q : V.toScheme ⟶ Y} {em : Y ⟶ Y'} [IsOpenImmersion em] (h : IsChart a b V q)
    (hc : V.ι ≫ π = q ≫ em) (hpre : π ⁻¹ᵁ em.opensRange = V) (w : a ≫ π = b ≫ π) :
    IsIso (pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V)) := by
  obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := h

  have h1 : IsPullback (b ∣_ V) (a' ≫ V.ι) (V.ι ≫ π) π := by
    have h0 := hsq.paste_horiz (isPullback_of_preimage_opensRange π V q em hc hpre).flip
    rw [← hc] at h0
    exact h0.flip

  have h2 : IsPullback (pullback.snd π π ∣_ V) ((pullback.snd π π ⁻¹ᵁ V).ι ≫ pullback.fst π π)
      (V.ι ≫ π) π :=
    (isPullback_morphismRestrict (pullback.snd π π) V).paste_vert (IsPullback.of_hasPullback π π).flip
  have hdom : pullback.lift a b w ⁻¹ᵁ (pullback.snd π π ⁻¹ᵁ V) = b ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_snd]

  have key : pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V) =
      (P.isoOfEq hdom).hom ≫ (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc]
      rw [IsPullback.isoIsPullback_hom_fst_assoc]
      simp only [morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.lift_snd,
        Scheme.isoOfEq_hom_ι_assoc]
    · rw [morphismRestrict_ι_assoc, pullback.lift_fst, Category.assoc,
        IsPullback.isoIsPullback_hom_snd, ha', Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance

theorem isPullback_of_isChart {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type}
    (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hch : ∀ j, IsChart a b (V j) (q j))
    (hc : ∀ j, (V j).ι ≫ π = q j ≫ em j) (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j)
    (hcov : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) : IsPullback a b π π := by

  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, z, hz⟩ := hcov (π x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨j, ?_⟩
    rw [← hpre j, Scheme.Hom.mem_preimage]
    exact ⟨z, hz⟩

  have hw : a ≫ π = b ≫ π := by
    refine Scheme.Cover.hom_ext
      (P.openCoverOfIsOpenCover (fun j => b ⁻¹ᵁ V j)
        (by unfold TopologicalSpace.IsOpenCover; exact b.iSup_preimage_eq_top hV)) _ _ fun j => ?_
    obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := hch j
    change (b ⁻¹ᵁ V j).ι ≫ a ≫ π = (b ⁻¹ᵁ V j).ι ≫ b ≫ π
    calc (b ⁻¹ᵁ V j).ι ≫ a ≫ π = a' ≫ (V j).ι ≫ π := by
          rw [← Category.assoc, ← ha', Category.assoc]
      _ = a' ≫ q j ≫ em j := by rw [hc j]
      _ = (b ∣_ V j) ≫ q j ≫ em j := by rw [← Category.assoc, hsq.w, Category.assoc]
      _ = (b ∣_ V j) ≫ (V j).ι ≫ π := by rw [hc j]
      _ = (b ⁻¹ᵁ V j).ι ≫ b ≫ π := by rw [morphismRestrict_ι_assoc]

  have hiso : IsIso (pullback.lift a b hw) := by
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun j => pullback.snd π π ⁻¹ᵁ V j) ((pullback.snd π π).iSup_preimage_eq_top hV)]
    intro j
    rw [MorphismProperty.isomorphisms.iff]
    exact IsChart.isIso_restrict_lift (hch j) (hc j) (hpre j) hw
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift a b hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.FreeQuotGlue
