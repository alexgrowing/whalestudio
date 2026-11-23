import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseChangeTestOfSurjectiveMulAbelianVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibres
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twhopf

open GlobalTheory.FibreFlat in
set_option backward.isDefEq.respectTransparency false in

theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : LocallyQuasiFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1)
      (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq h2)
      (fun k _ t => ?_) ⟨_, rfl⟩
    intro W Z a b j h sq2 e
    refine ((H k (t ≫ u)).target sq) a b j h sq2 ?_
    rw [pullback.condition, reassoc_of% e]
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i))
      (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq h2) (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Algebra.QuasiFinite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  refine GlobalTheory.flat_of_quasiFinite_of_flat_fibres R A B fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

theorem mul_flat : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left := by
  intro S _ G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have hq : LocallyQuasiFinite ((𝟙 G) ^ N).left := locallyQuasiFinite_pow_semiAbelian S G hG N hN
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  exact flat_of_flatOver_fields _ G.hom inferInstance (by rw [Over.w]; infer_instance)
    (by rw [Over.w]; infer_instance) hq fun k _ s =>
      GlobalTheory.FibreFlat.flatOver_of_pullback _ s (GlobalTheory.IntDiv.flat_fibre G _ k s)

theorem points_div : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of V) ⟶ S) (N : ℕ), 1 ≤ N → ∀ c : Over.mk x ⟶ G, ∃ c' : Over.mk x ⟶ G, c' ^ N = c := by
  intro V _ _ _ _ S _ G _ hG x N hN c
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hi := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  let φ : G ⟶ G := (𝟙 G) ^ N
  have hφ : mulN G N = φ := by
    have := GlobalTheory.ZJ.OmTest.comp_mulN (𝟙 G) N
    rwa [Category.id_comp] at this
  have hq : LocallyQuasiFinite φ.left := locallyQuasiFinite_pow_semiAbelian S G hG N hN
  have hf : Flat φ.left := mul_flat S G hG N hN
  have : LocallyOfFiniteType (φ.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (φ.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact φ.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (φ.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated φ.left := IsSeparated.of_comp _ G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : LocallyOfFinitePresentation φ.left := inferInstance
  have ho : IsOpen (Set.range φ.left) := φ.left.isOpenMap.isOpen_range
  have hs : Function.Surjective φ.left := by
    have := GlobalTheory.ZJ.OmTest.surjective_mulN G N (by rw [hφ]; exact ho)
    rwa [hφ] at this
  obtain ⟨g, hg⟩ := hs (c.left (IsLocalRing.closedPoint V))
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := c.left) g
    (IsLocalRing.closedPoint V) hg
  obtain ⟨s, hs', -⟩ := GlobalTheory.exists_section_of_quasiFinite_flat V (FractionRing V) _
    (pullback.snd φ.left c.left) z hz
  have e : (s ≫ pullback.fst φ.left c.left) ≫ φ.left = c.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst φ.left c.left) ?_, ?_⟩
  · have h1 := Over.w φ
    have h2 := Over.w c
    rw [← h1, ← Category.assoc, e]
    exact h2
  · rw [← Category.comp_id (Over.homMk _ _), ← MonObj.comp_pow]
    exact Over.OverMorphism.ext e

end PositivityTheory.HtPt.Twhopf
