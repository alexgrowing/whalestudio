import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_schemeTheoreticallyDominant {W Y X Z : Scheme.{0}} (φ : W ⟶ Y)
    [IsSchemeTheoreticallyDominant φ] (i : Z ⟶ X) [IsClosedImmersion i] (a : Y ⟶ X) (c : W ⟶ Z)
    (h : c ≫ i = φ ≫ a) : ∃ b : Y ⟶ Z, b ≫ i = a := by
  have H : i.ker ≤ a.ker := by
    have h1 : i.ker ≤ (c ≫ i).ker := Scheme.Hom.le_ker_comp c i
    rwa [h, ← Scheme.IdealSheafData.map_ker, φ.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h1
  exact ⟨IsClosedImmersion.lift i a H, IsClosedImmersion.lift_fac i a H⟩

theorem over_ext_of_schemeTheoreticallyDominant {S W : Scheme.{0}} {Y X : Over S}
    [IsSeparated X.hom] (φ : W ⟶ Y.left) [IsSchemeTheoreticallyDominant φ] {a b : Y ⟶ X}
    (h : φ ≫ a.left = φ ≫ b.left) : a = b := by
  have hY : a.left ≫ X.hom = b.left ≫ X.hom := by rw [Over.w a, Over.w b]
  let e : Y.left ⟶ pullback X.hom X.hom := pullback.lift a.left b.left hY
  have he1 : e ≫ pullback.fst X.hom X.hom = a.left := pullback.lift_fst _ _ _
  have he2 : e ≫ pullback.snd X.hom X.hom = b.left := pullback.lift_snd _ _ _
  have hc : (φ ≫ a.left) ≫ pullback.diagonal X.hom = φ ≫ e := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullback.diagonal_fst, he1, Category.comp_id]
    · simp only [Category.assoc]
      rw [pullback.diagonal_snd, he2, Category.comp_id, h]
  have hs2 : pullback.lift (φ ≫ a.left) φ hc ≫ pullback.snd (pullback.diagonal X.hom) e = φ :=
    pullback.lift_snd _ _ _
  obtain ⟨s, hs⟩ := exists_lift_of_schemeTheoreticallyDominant φ
    (pullback.snd (pullback.diagonal X.hom) e) (𝟙 _) (pullback.lift _ _ hc)
    (by rw [hs2, Category.comp_id])
  have key : ∀ g : pullback X.hom X.hom ⟶ X.left, e ≫ g =
      s ≫ pullback.fst (pullback.diagonal X.hom) e ≫ pullback.diagonal X.hom ≫ g := by
    intro g
    rw [pullback.condition_assoc, ← Category.assoc s, hs, Category.id_comp]
  have ha := key (pullback.fst X.hom X.hom)
  have hb := key (pullback.snd X.hom X.hom)
  rw [he1, pullback.diagonal_fst, Category.comp_id] at ha
  rw [he2, pullback.diagonal_snd, Category.comp_id] at hb
  exact Over.OverMorphism.ext (ha.trans hb.symm)

section

variable {S S' : Scheme.{0}} (f : S' ⟶ S) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]

theorem pullback_map_injective_of_flat {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom]
    {a b : Y ⟶ X} (h : (Over.pullback f).map a = (Over.pullback f).map b) : a = b := by
  apply over_ext_of_schemeTheoreticallyDominant (pullback.fst Y.hom f)
  have ka : ((Over.pullback f).map a).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have kb : ((Over.pullback f).map b).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ b.left :=
    pullback.lift_fst _ _ _
  rw [← ka, ← kb, h]

theorem existsUnique_lift_of_flat {Y X Z : Over S} (i : Z ⟶ X) (a : Y ⟶ X)
    (a' : (Over.pullback f).obj Y ⟶ (Over.pullback f).obj Z) [Flat Y.hom]
    [IsClosedImmersion i.left] (h : a' ≫ (Over.pullback f).map i = (Over.pullback f).map a) :
    ∃! b : Y ⟶ Z, b ≫ i = a ∧ (Over.pullback f).map b = a' := by
  have ki : ((Over.pullback f).map i).left ≫ pullback.fst X.hom f = pullback.fst Z.hom f ≫ i.left :=
    pullback.lift_fst _ _ _
  have ka : ((Over.pullback f).map a).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have hc : (a'.left ≫ pullback.fst Z.hom f) ≫ i.left = pullback.fst Y.hom f ≫ a.left := by
    rw [Category.assoc, ← ki, ← ka, ← h, Over.comp_left, Category.assoc]
  obtain ⟨b₀, hb₀⟩ := exists_lift_of_schemeTheoreticallyDominant (pullback.fst Y.hom f) i.left
    a.left (a'.left ≫ pullback.fst Z.hom f) hc
  have hw : b₀ ≫ Z.hom = Y.hom := by
    rw [← Over.w i, ← Category.assoc, hb₀, Over.w a]
  have kb1 : ((Over.pullback f).map (Over.homMk b₀ hw)).left ≫ pullback.fst Z.hom f =
      pullback.fst Y.hom f ≫ b₀ := pullback.lift_fst _ _ _
  have kb2 : ((Over.pullback f).map (Over.homMk b₀ hw)).left ≫ pullback.snd Z.hom f =
      pullback.snd Y.hom f := pullback.lift_snd _ _ _
  have h3 : a'.left ≫ pullback.snd Z.hom f = pullback.snd Y.hom f := Over.w a'
  refine ⟨Over.homMk b₀ hw, ⟨Over.OverMorphism.ext hb₀, ?_⟩, ?_⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [← cancel_mono i.left, kb1, Category.assoc, Category.assoc, hb₀, ← hc, Category.assoc]
    · rw [kb2, h3]
  · rintro b ⟨hb, -⟩
    apply Over.OverMorphism.ext
    rw [← cancel_mono i.left]
    have hb' := congrArg CommaMorphism.left hb
    exact hb'.trans hb₀.symm

theorem isMonHom_of_pullback_of_flat {G G' : Over S} [MonObj G] [MonObj G'] (F : G ⟶ G')
    [Flat G.hom] [IsSeparated G'.hom] [h : IsMonHom ((Over.pullback f).map F)] : IsMonHom F := by
  have h1 : Flat (𝟙_ (Over S)).hom := by
    change Flat (𝟙 S)
    infer_instance
  have h2 : Flat (G ⊗ G).hom := by
    change Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  constructor
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.one_hom ((Over.pullback f).map F)
    simp only [Functor.obj.η_def, Category.assoc] at this
    rw [Functor.map_comp]
    exact (cancel_epi _).1 this
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.mul_hom ((Over.pullback f).map F)
    simp only [Functor.obj.μ_def, Category.assoc] at this
    rw [Functor.LaxMonoidal.μ_natural_assoc] at this
    rw [Functor.map_comp, Functor.map_comp]
    exact (cancel_epi _).1 this

end

theorem schemeTheoreticallyDominant_fractionField (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] :
    IsSchemeTheoreticallyDominant (spMap (algebraMap T K)) := by
  have hinj : Function.Injective (algebraMap T K) := IsFractionRing.injective T K
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap T K))
  have h : Function.Injective (spMap (algebraMap T K)).appTop := by
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e] at h2
    simp only at h2
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of T)).hom).1 (hinj h2)
  refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [Scheme.Hom.ker_apply _ ⟨⊤, isAffineOpen_top _⟩]
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).1 h

theorem flat_dvr_generic_fibre :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X : Over (Sp T)), Flat Y.hom → IsSeparated X.hom → ∀ a b : Y ⟶ X, (Over.pullback (spMap (algebraMap T K))).map a = (Over.pullback (spMap (algebraMap T K))).map b → a = b) ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X Ga : Over (Sp T)) (io : Ga ⟶ X) (a : Y ⟶ X) (a' : (Over.pullback (spMap (algebraMap T K))).obj Y ⟶ (Over.pullback (spMap (algebraMap T K))).obj Ga), Flat Y.hom → IsClosedImmersion io.left → a' ≫ (Over.pullback (spMap (algebraMap T K))).map io = (Over.pullback (spMap (algebraMap T K))).map a → ∃! b : Y ⟶ Ga, b ≫ io = a ∧ (Over.pullback (spMap (algebraMap T K))).map b = a') ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'] (F : G ⟶ G'), Flat G.hom → IsSeparated G'.hom → IsMonHom ((Over.pullback (spMap (algebraMap T K))).map F) → IsMonHom F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T K _ _ _ _ _ _ Y X hY hX a b h
    have := schemeTheoreticallyDominant_fractionField T K
    exact pullback_map_injective_of_flat (spMap (algebraMap T K)) h
  · intro T K _ _ _ _ _ _ Y X Ga io a a' hY hio h
    have := schemeTheoreticallyDominant_fractionField T K
    exact existsUnique_lift_of_flat (spMap (algebraMap T K)) io a a' h
  · intro T K _ _ _ _ _ _ G G' _ _ F hG hG' hF
    have := schemeTheoreticallyDominant_fractionField T K
    exact isMonHom_of_pullback_of_flat (spMap (algebraMap T K)) F

end GlobalTheory
