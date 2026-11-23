import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfNbhd

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem off_map_le {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (J : Ideal A) :
    off B (J.map φ) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A J := by
  intro x hx
  change x ∈ (PrimeSpectrum.zeroLocus _)ᶜ at hx
  change PrimeSpectrum.comap φ x ∈ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  intro h; apply hx
  rw [PrimeSpectrum.mem_zeroLocus] at h
  exact (Ideal.map_le_iff_le_comap.2 h : J.map φ ≤ _)

theorem opnMap_comp' {X'' X' X : Scheme.{0}} (k : X'' ⟶ X) (g : X'' ⟶ X') (f : X' ⟶ X) (hk : k = g ≫ f)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h1 : U'' ≤ g ⁻¹ᵁ U') (h2 : U' ≤ f ⁻¹ᵁ U)
    (h : U'' ≤ k ⁻¹ᵁ U) : opnMap k U'' U h = opnMap g U'' U' h1 ≫ opnMap f U' U h2 := by
  subst hk
  apply Arrow.hom_ext
  · change sch.map (Scheme.Hom.resLE (g ≫ f) U U'' h) =
      sch.map (Scheme.Hom.resLE g U' U'' h1) ≫ sch.map (Scheme.Hom.resLE f U U' h2)
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map (g ≫ f) = sch.map g ≫ sch.map f
    exact Functor.map_comp _ _ _

theorem leafExcAff_pf : LeafExcAff := by
  intro hyp hIE d q _ R B C _ _ _ ψ η hq hψ I K hη hK hI
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI; subst hK
  have hJfg : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hIfg := hJfg.map ψ
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by
    simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqB : IsUnit (q : B) := by simpa using hqP.map ψ
  have e1 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q ψ _ hJfg (indNbhd_of_nbhd ψ _ hψ) hqP (off_map_le ψ _)
  have e2 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q η _ hIfg hη hqB (off_map_le η _)
  have hle : off C ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ |>.map η) ≤
      Spec.map (CommRingCat.ofHom (η.comp ψ)) ⁻¹ᵁ off _ (Ideal.span (Set.range MvPolynomial.X)) := by
    rw [Ideal.map_map]; exact off_map_le _ _
  refine ⟨hle, ?_⟩
  have hs : Spec.map (CommRingCat.ofHom (η.comp ψ)) =
      Spec.map (CommRingCat.ofHom η) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp]; rfl
  rw [opnMap_comp' _ _ _ hs _ _ _ (off_map_le η _) (off_map_le ψ _)]
  exact exc_comp q e2 e1

end LateralTheory.CohomologicalPurity.TubeCut
