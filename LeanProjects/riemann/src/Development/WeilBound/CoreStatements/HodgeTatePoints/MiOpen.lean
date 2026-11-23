import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace PositivityTheory.HtPt.Mi

theorem flat_of_forall {X Z : Scheme.{0}} (f : X ⟶ Z)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (g : W ⟶ X) (w : W), g w = x ∧ Flat g ∧ Flat (g ≫ f)) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨W, g, w, rfl, _, _⟩ := h x
  have h := Flat.stalkMap (g ≫ f) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact GlobalTheory.ringHom_flat_of_comp_faithfullyFlat (GlobalTheory.faithfullyFlat_stalkMap_of_flat g w) h

theorem open_crit : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  intro R _ X Y j q _ H
  have key : ∀ x : X, ∃ (U V : Scheme.{0}) (g : U ⟶ X) (u : U) (δ : U ⟶ V) (m : V ⟶ pullback j j),
      g u = x ∧ Flat g ∧ Flat (g ≫ j) ∧ IsOpenImmersion δ ∧ Flat m ∧ δ ≫ m = g ≫ pullback.diagonal j ∧
      ∀ z, pullback.snd j j z = x → ∃ u', m (δ u') = z := by
    intro x
    obtain ⟨R', _, _, _, X', Y', j', q', a, b, U, hfl, hP, hb, ha, hU, hcl⟩ := @H (q (j x)).asIdeal (q (j x)).isPrime
    have hs : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 hfl)
    have hbf : Flat b := MorphismProperty.of_isPullback hb.flip hs
    have haf : Flat a := MorphismProperty.of_isPullback ha.flip hbf
    obtain ⟨x', hx1, hx2⟩ := Scheme.exists_preimage_of_isPullback (ha.paste_vert hb) x
      (IsLocalRing.closedPoint R') (PrimeSpectrum.ext hP.symm)
    have hx2' : q' (j' x') = IsLocalRing.closedPoint R' := by rw [← hx2]; simp
    let u : U.toScheme := ⟨x', hcl x' hx2'⟩
    have hu : U.ι u = x' := rfl
    have hw : (U.ι ≫ a) ≫ j = (U.ι ≫ j') ≫ b := by rw [Category.assoc, ha.w, Category.assoc]
    let δ : U.toScheme ⟶ pullback j' (U.ι ≫ j') := pullback.lift U.ι (𝟙 _) (by simp)
    have hδ : δ ≫ pullback.fst _ _ = U.ι := pullback.lift_fst _ _ _
    have hδ' : δ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hV := (IsPullback.of_hasPullback j' (U.ι ≫ j')).paste_horiz ha
    rw [← hw] at hV
    let m : pullback j' (U.ι ≫ j') ⟶ pullback j j :=
      pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ U.ι ≫ a) (by rw [hV.w]; simp only [Category.assoc])
    have hm1 : m ≫ pullback.fst j j = pullback.fst _ _ ≫ a := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd j j = pullback.snd _ _ ≫ U.ι ≫ a := pullback.lift_snd _ _ _
    have hm : IsPullback m (pullback.snd j' (U.ι ≫ j')) (pullback.snd j j) (U.ι ≫ a) :=
      IsPullback.of_right (by rw [hm1]; exact hV) hm2 (IsPullback.of_hasPullback j j)
    have hg : Flat (U.ι ≫ a) := inferInstance
    have hδo : IsOpenImmersion δ := by
      have : IsOpenImmersion (δ ≫ pullback.fst j' (U.ι ≫ j')) := by rw [hδ]; infer_instance
      exact IsOpenImmersion.of_comp δ (pullback.fst j' (U.ι ≫ j'))
    have hgu : (U.ι ≫ a) u = x := by rw [Scheme.Hom.comp_apply, hu]; exact hx1
    refine ⟨U, _, U.ι ≫ a, u, δ, m, hgu, hg, by rw [hw]; infer_instance, hδo,
      MorphismProperty.of_isPullback hm.flip hg, ?_, fun z hz => ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, reassoc_of% hδ]; simp
      · rw [Category.assoc, hm2, reassoc_of% hδ']; simp
    · obtain ⟨v, hv1, hv2⟩ := Scheme.exists_preimage_of_isPullback hm z u (hz.trans hgu.symm)
      have h1 : j' (pullback.fst j' (U.ι ≫ j') v) = j' x' := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact congrArg (fun t => j' (U.ι t)) hv2
      let u' : U.toScheme := ⟨pullback.fst j' (U.ι ≫ j') v, hcl _ (by rw [h1, hx2'])⟩
      have h2 : δ u' = v := by
        apply (pullback.fst j' (U.ι ≫ j')).isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hδ]
        rfl
      exact ⟨u', by rw [h2]; exact hv1⟩
  have : Flat j := flat_of_forall j fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, h3, -⟩ := key x
    exact ⟨U, g, u, h1, h2, h3⟩
  have : Flat (pullback.diagonal j) := flat_of_forall _ fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, -, h4, h5, h6, -⟩ := key x
    exact ⟨U, g, u, h1, h2, by rw [← h6]; infer_instance⟩
  have : Surjective (pullback.diagonal j) := ⟨fun z => by
    obtain ⟨U, V, g, u, δ, m, -, -, -, -, -, h6, h7⟩ := key (pullback.snd j j z)
    obtain ⟨u', hu'⟩ := h7 z rfl
    exact ⟨g u', by rw [← hu', ← Scheme.Hom.comp_apply, ← h6, Scheme.Hom.comp_apply]⟩⟩
  have : IsClosedImmersion (pullback.diagonal j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [(pullback.diagonal j).surjective.range_eq]; exact isClosed_univ)
  have : IsIso (pullback.diagonal j) := Flat.isIso_of_surjective_of_mono _
  have : Mono j := (pullback.isIso_diagonal_iff j).1 this
  exact IsOpenImmersion.of_flat_of_mono j

end PositivityTheory.HtPt.Mi
