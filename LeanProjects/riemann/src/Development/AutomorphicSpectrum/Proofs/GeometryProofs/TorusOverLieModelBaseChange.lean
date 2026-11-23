import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC

open GlobalTheory.CompanionTheory.Ar.TorusModel

theorem pt_ext {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap e) φ) {T : Over (Sp L')} (u v : T ⟶ G')
    (huv : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext huv (by rw [Over.w u, Over.w v]))

theorem isTanAt_comp {S : Scheme.{0}} {R : Type} [CommRing R] {H G : Over S} [GrpObj H] [GrpObj G] (i : H ⟶ G)
    [IsMonHom i] (x : Sp R ⟶ S) (v : epsAt x ⟶ H) (hv : IsTanAt H x v) : IsTanAt G x (v ≫ i) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem dualMap_cast {L L' : Type} [Field L] [Field L'] (e : L →+* L') (n : ℤ) :
    dualMap e (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (n : L)) =
      TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (n : L') := by
  ext <;> simp [dualMap]

theorem base_comm {L L' : Type} [Field L] [Field L'] (e : L →+* L') :
    spMap (dualMap e) ≫ Spec.map (CommRingCat.ofHom (algebraMap L (DualNumber L))) ≫ 𝟙 (Sp L) =
      (Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e := by
  simp only [Category.comp_id, Category.id_comp]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem push_eq {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] (φ : G'.left ⟶ G.left) {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (i : splitTorus (Sp L) X ⟶ G) (i' : splitTorus (Sp L') X' ⟶ G') (κ : X ≃+ X')
    (hκ : ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Sp L') (t' : Over.mk a ⟶ splitTorus (Sp L') X')
      (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X), (∀ χ, charVal t χ = charVal t' (κ χ)) →
        (t' ≫ i').left ≫ φ = (t ≫ i).left)
    (MT : LieModel (splitTorus (Sp L) X) (𝟙 _) (X →+ L)) (hMT : IsCocharLie MT)
    (MT' : LieModel (splitTorus (Sp L') X') (𝟙 _) (X' →+ L')) (hMT' : IsCocharLie MT') (δ : X →+ ℤ) :
    (MT'.pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom)) ≫ i').left ≫ φ =
      spMap (dualMap e) ≫ (MT.pt ((Int.castAddHom L).comp δ) ≫ i).left := by
  set c := (Int.castAddHom L).comp δ with hc
  have hw : spMap (dualMap e) ≫ (MT.pt c).left ≫ (splitTorus (Sp L) X).hom =
      (Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e := by
    rw [Over.w (MT.pt c)]
    exact base_comm e
  let t : Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e) ⟶
      splitTorus (Sp L) X := Over.homMk (spMap (dualMap e) ≫ (MT.pt c).left) (by simpa using hw)
  have h := hκ (DualNumber L') _ (MT'.pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom))) t (fun χ => by
    rw [charVal_comp (dualMap e) (MT.pt c) t rfl χ, hMT c χ, hMT' _ (κ χ)]
    simpa [hc] using dualMap_cast e (δ χ))
  rw [h]
  simp [t]

theorem cochars_baseChange : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (τ : TorusExtension G) (τ' : TorusExtension G'), IsGrpPullback G' G (spMap e) φ → GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e τ τ' φ → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → ∀ I : AddSubgroup V, (letI := τ.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L), IsCocharLie MT ∧ ∀ x, x ∈ I ↔ ∃ δ : τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i) → (letI := τ'.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L') τ'.X) (𝟙 _) (τ'.X →+ L'), IsCocharLie MT ∧ ∀ x, x ∈ I.map j ↔ ∃ δ : τ'.X →+ ℤ, MV'.pt x = MT.pt ((Int.castAddHom L').comp δ) ≫ τ'.i) := by
  intro L L' _ _ e G G' _ _ φ τ τ' hP hTO V V' _ _ _ _ MV MV' j hj I hI
  letI := τ.addCommGroup
  letI := τ'.addCommGroup
  obtain ⟨κ, hκ⟩ := hTO
  obtain ⟨MT, hMT, hI⟩ := hI
  have hM' := isCocharLie_lieModel (X := τ'.X) (𝟙 (Sp L'))
  have hi := τ.i_hom
  have hp := fun δ => push_eq e φ τ.i τ'.i κ hκ MT hMT (lieModel (𝟙 (Sp L'))) hM' δ
  have hfw : ∀ (x : V) (δ : τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i →
      MV'.pt (j x) = (lieModel (𝟙 (Sp L'))).pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom)) ≫ τ'.i := by
    intro x δ hx
    refine pt_ext e hP _ _ ?_
    rw [hj x, hx, hp δ]
  refine ⟨lieModel (𝟙 (Sp L')), hM', fun x' => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨δ, hδ⟩ := (hI x).1 hx
    exact ⟨_, hfw x δ hδ⟩
  · rintro ⟨δ', hδ'⟩
    set δ : τ.X →+ ℤ := δ'.comp κ.toAddMonoidHom with hδ
    obtain ⟨x, hx⟩ := MV.onto _ (isTanAt_comp τ.i _ _ (MT.tan ((Int.castAddHom L).comp δ)))
    refine ⟨x, (hI x).2 ⟨δ, hx⟩, MV'.inj ?_⟩
    rw [hfw x δ hx, hδ', hδ]
    congr 3
    ext χ
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC
