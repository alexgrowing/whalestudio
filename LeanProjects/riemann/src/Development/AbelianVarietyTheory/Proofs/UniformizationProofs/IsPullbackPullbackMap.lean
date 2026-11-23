import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusExtBaseChange

theorem isPullback_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h1 : ((Over.pullback f).map q).left ≫ pullback.fst B.hom f = pullback.fst G.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback B.hom f)
  rw [h2, Over.w q]
  exact IsPullback.of_hasPullback _ _

theorem exists_extension {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    {T' G' B' : Over S'} [GrpObj T'] [GrpObj G'] [GrpObj B']
    (eT : T' ≅ (Over.pullback f).obj T) (eG : G' ≅ (Over.pullback f).obj G)
    (eB : B' ≅ (Over.pullback f).obj B) [IsMonHom eT.hom] [IsMonHom eG.hom] [IsMonHom eB.hom]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] (hf : Flat q.left) (hs : Surjective q.left)
    (ha : IsAffineHom q.left) (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : T' ⟶ G'), IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧
      IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] ∧
      q'.left ≫ eB.hom.left ≫ pullback.fst B.hom f = (eG.hom.left ≫ pullback.fst G.hom f) ≫ q.left ∧
      i'.left ≫ eG.hom.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst T.hom f) ≫ i.left := by
  have pq := isPullback_pullback_map f q
  have pi := isPullback_pullback_map f i
  have iG : IsIso eG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eG.hom))
  have iB : IsIso eB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eB.inv))
  have hf' : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hf
  have hs' : Surjective ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hs
  have ha' : IsAffineHom ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq ha
  refine ⟨eG.hom ≫ (Over.pullback f).map q ≫ eB.inv, eT.hom ≫ (Over.pullback f).map i ≫ eG.inv,
    inferInstance, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · refine (hk.map (Over.pullback f)).of_iso eT.symm eG.symm
      (Functor.Monoidal.εIso (Over.pullback f)).symm eB.symm ?_ (toUnit_unique _ _) ?_ ?_
    · simp
    · simp
    · have : η[(Over.pullback f).obj B] ≫ eB.inv = η[B'] := IsMonHom.one_hom _
      rw [← this, Functor.obj.η_def]
      simp
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pq.w]
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eG.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pi.w]

theorem exists_iso_of_square {S S' S₀ S₀' : Scheme.{0}} (f : S' ⟶ S) (f₀ : S₀' ⟶ S₀) (j : S₀ ⟶ S)
    (j' : S₀' ⟶ S') (w : j' ≫ f = f₀ ≫ j) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ e : (Over.pullback j').obj G' ≅ (Over.pullback f₀).obj ((Over.pullback j).obj G), IsMonHom e.hom ∧
      e.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom f₀ ≫ pullback.fst G.hom j =
        pullback.fst G'.hom j' ≫ bc.hom.left ≫ pullback.fst G.hom f :=
  Geo.Tor.grpPullback_iso
    (((Geo.Tor.isGrpPullback_pullback G' j').comp
      (((Geo.Tor.isGrpPullback_of_iso bc).comp (Geo.Tor.isGrpPullback_pullback G f)).congr
        (Category.id_comp _) rfl)).congr w rfl)
    ((Geo.Tor.isGrpPullback_pullback _ f₀).comp (Geo.Tor.isGrpPullback_pullback G j))

theorem exists_splitTorus_iso {S S' : Scheme.{0}} (f : S' ⟶ S) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (xe : X' ≃+ X) :
    ∃ e : splitTorus S' X' ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ x : X', (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X (xe x)).val =
        (charUnit S' X' x).val := by
  obtain ⟨e, he, hc⟩ := splitTorus_baseChange S S' f X
  let e₀ : splitTorus S' X' ≅ splitTorus S' X :=
    { hom := SplitTorus.torusMap S' xe.symm.toAddMonoidHom
      inv := SplitTorus.torusMap S' xe.toAddMonoidHom
      hom_inv_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp
      inv_hom_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp }
  have : IsMonHom e₀.hom := SplitTorus.isMonHom_torusMap _
  refine ⟨e₀ ≪≫ e, inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom)), fun x => ?_⟩
  rw [Iso.trans_hom, Over.comp_left, Category.assoc, Rosenlicht.appTop_comp_apply, hc,
    SplitTorus.charUnit_val, SplitTorus.charUnit_val]
  refine (SplitTorus.torusMap_appTop_chi xe.symm.toAddMonoidHom (xe x)).trans ?_
  simp

end TorusExtBaseChange

open TorusExtBaseChange in

theorem gtCoord_baseChange_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R'), I.map φ ≤ I' → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (e : ℕ) (g : GtCoord I D e G), ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (q' : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A) (i' : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G'), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧ IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' (η[thickObj R' I' e D'.P.A]) ∧ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ g.pG.left ∧ ∃ hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, i'.left ≫ h = hT ≫ g.i.left ∧ ∀ x : D'.X, hT.appTop.hom (charUnit _ D.X (hD.xe x)).val = (charUnit _ D'.X x).val := by
  intro R R' _ _ _ _ φ D D' hD I I' hI G _ _ G' _ _ bc hbc e g
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI _
  let f₀ : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ hle))
  have w : thick R' I' e ≫ specOf φ = f₀ ≫ thick R I e := by
    simp only [f₀, thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  have := hD.e_hom
  have := g.q_hom
  have := g.i_hom
  obtain ⟨eG, mG, hG⟩ := exists_iso_of_square _ f₀ _ _ w G G' bc
  obtain ⟨eB, mB, hB⟩ := exists_iso_of_square _ f₀ _ _ w D.P.A D'.P.A hD.e
  obtain ⟨eT, mT, hT⟩ := exists_splitTorus_iso f₀ hD.xe
  obtain ⟨q', i', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_extension f₀ eT eG eB g.i g.q g.q_flat g.q_surj g.q_affine g.isKernel
  refine ⟨eG.hom.left ≫ pullback.fst _ f₀, q', i', ?_, h1, h2, h3, h4, h5, h6, ?_, _, h8, hT⟩
  · exact (Category.assoc _ _ _).trans hG
  · change (q'.left ≫ pullback.fst D'.P.A.hom (thick R' I' e)) ≫ _ =
      _ ≫ g.q.left ≫ pullback.fst D.P.A.hom (thick R I e)
    rw [Category.assoc, ← hB, ← Category.assoc _ g.q.left, ← h7]
    simp only [Category.assoc]

end GlobalTheory
