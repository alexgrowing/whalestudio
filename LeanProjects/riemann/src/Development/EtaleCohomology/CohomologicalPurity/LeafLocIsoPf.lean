import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

noncomputable section
namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesPullbacks : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ SimplicialObject.const PSh))

theorem pbRel_isIso_of {B G E' E Q₁ Q₀ : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    {f₁ : Q₁ ⟶ E'} {z₁ : Q₁ ⟶ G} {f₀ : Q₀ ⟶ E} {z₀ : Q₀ ⟶ G} (h₁ : IsPullback f₁ z₁ π' g) (h₀ : IsPullback f₀ z₀ π g)
    (k : Q₁ ⟶ Q₀) [IsIso k] (kf : k ≫ f₀ = f₁ ≫ a) (kz : k ≫ z₀ = z₁) : IsIso (pbRel g a π' π h) := by
  have e : h₁.isoPullback.hom ≫ pbRel g a π' π h = k ≫ h₀.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pbRel, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, kf]
    · simp only [pbRel, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd, kz, Category.comp_id]
  have e' : pbRel g a π' π h = h₁.isoPullback.inv ≫ k ≫ h₀.isoPullback.hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [e']; infer_instance

theorem isIso_specMap_of_bij {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hb : Function.Bijective f) :
    IsIso (Spec.map (CommRingCat.ofHom f)) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hb).toCommRingCatIso.isIso_hom
  infer_instance

theorem quot_bij_of_eq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I J : Ideal A) (e : J = I) (K : Ideal B)
    (hK : K = I.map φ) (h : J ≤ K.comap φ) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap K φ h) := by
  subst e; subst hK; exact hb

theorem LeafLocIso_of (hZ : LeafZ) (hQ : LeafQuot) : LeafLocIso := by
  intro H d P V h
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ : A →+* H.obj A I := eta H P V
  obtain ⟨⟨z₁, h₁⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj A I) φ
  obtain ⟨⟨z₀, h₀'⟩, -⟩ := hZ P.X P.Z P.ι V A (RingHom.id A)
  have e₀ : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ V.2.fromSpec = V.2.fromSpec := by simp
  rw [e₀] at h₀'
  have hle : I.map (RingHom.id A) ≤ (I.map φ).comap φ := by rw [Ideal.map_id]; exact Ideal.le_comap_map
  set qm := Ideal.quotientMap (I.map φ) φ hle
  have hb : Function.Bijective qm := quot_bij_of_eq φ I _ (Ideal.map_id I) _ rfl hle (hQ A (H.obj A I) φ I (H.ind A I))
  have hcomp : qm.comp (Ideal.Quotient.mk (I.map (RingHom.id A))) = (Ideal.Quotient.mk (I.map φ)).comp φ :=
    Ideal.quotientMap_comp_mk hle
  have kf : Spec.map (CommRingCat.ofHom qm) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (RingHom.id A)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have kz : Spec.map (CommRingCat.ofHom qm) ≫ z₀ = z₁ := by
    rw [← cancel_mono P.ι, Category.assoc, ← h₀'.w, ← h₁.w, ← Category.assoc, kf, Category.assoc]
  have := isIso_specMap_of_bij qm hb
  exact pbRel_isIso_of _ _ _ _ h (h₁.map sch) (h₀'.map sch) (sch.map (Spec.map (CommRingCat.ofHom qm)))
    (by rw [← sch.map_comp, kf, sch.map_comp]) (by rw [← sch.map_comp, kz])

end LateralTheory.CohomologicalPurity.TubeCut
