import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def LineChart : Prop := ∀ {L S : Scheme.{0}} (l : L ⟶ S), IsLine l → ∀ (R : Type) [CommRing R]
  (j0 : Spec (CommRingCat.of R) ⟶ S), IsOpenImmersion j0 →
    ∃ j : Spec (CommRingCat.of (Polynomial R)) ⟶ L, IsOpenImmersion j ∧
      j ≫ l = Spec.map (CommRingCat.ofHom Polynomial.C) ≫ j0

theorem chart_of (hEx : LineEx) (hLC : LineChart) : Chart := by
  intro A _ n
  induction n with
  | zero =>
    let E := (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv.toCommRingCatIso
    have hE : E.hom = CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin 0) A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.commutes a
    refine ⟨Spec (CommRingCat.of A), 𝟙 _, Spec.map E.hom, IterLine.iso _ inferInstance, inferInstance, ?_⟩
    rw [Category.comp_id, hE]
  | succ n ih =>
    obtain ⟨P, q, j, hq, hj, hjq⟩ := ih
    obtain ⟨L, l, hl⟩ := hEx P
    obtain ⟨j1, hj1, hj1l⟩ := hLC l hl (MvPolynomial (Fin n) A) j hj
    let F := (MvPolynomial.finSuccEquiv A n).symm
    let E := F.toRingEquiv.toCommRingCatIso
    have hE : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom Polynomial.C ≫ E.hom =
        CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin (n + 1)) A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have h1 : (Polynomial.C (algebraMap A (MvPolynomial (Fin n) A) a)) =
          algebraMap A (Polynomial (MvPolynomial (Fin n) A)) a := rfl
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      rw [h1]
      exact F.commutes a
    have hj1' := hj1
    refine ⟨L, l ≫ q, Spec.map E.hom ≫ j1, IterLine.comp l q hl hq, inferInstance, ?_⟩
    rw [Category.assoc, reassoc_of% hj1l, hjq, ← hE, Spec.map_comp, Spec.map_comp, Category.assoc]

end LateralTheory.E.EmbedPf
