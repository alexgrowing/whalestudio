import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSysGlobalModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitSemi

theorem spMap_comp'' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem exists_int_map (F : Type) [Field F] [NumberField F] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (g : F →+* FractionRing V) :
    ∃ oV : 𝓞 F →+* V, (algebraMap V (FractionRing V)).comp oV = g.comp (algebraMap (𝓞 F) F) := by
  have hint : ∀ a : 𝓞 F, ∃ r : V, algebraMap V (FractionRing V) r = g a := fun a => by
    have h2 : IsIntegral V (g a) := by
      obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom V), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap V (FractionRing V)).comp (Int.castRingHom V))
        (g.comp (algebraMap ℤ F)), ← Polynomial.hom_eval₂, h0, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 h2
  choose f hf using hint
  have hi := IsFractionRing.injective V (FractionRing V)
  let b : 𝓞 F →+* V :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun _ _ => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun _ _ => hi (by simp [hf]) }
  refine ⟨b, ?_⟩
  ext a
  exact hf a

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_genOf_of_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (y : Sp (FractionRing V) ⟶ Xo.XF c) : ∃ t : SAB H (Sp V), GenOf Xo c y t := by
  obtain ⟨g, hg⟩ := GlobalTheory.Models.RankZero.exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨oV, hoV⟩ := exists_int_map c.F V g
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, hG⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c (𝓞 c.F) _ Y V (FractionRing V) oV g y hoV hg
  obtain ⟨G, ⟨m⟩⟩ := hG yt
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull y Y.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m n₁
  have hy' : y ≫ Y.jQ ≫ pullback.fst _ _ = jK V ≫ yt := hyt.symm
  rw [hy'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap n₁
  exact ⟨G, _, ⟨mK⟩, ⟨mx⟩⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_finite_point' {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp'']

theorem exists_closure_finite (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, RingHom.finite_algebraMap.2 inferInstance, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

theorem finite_surjective_spMap {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F'] (h : F ≤ F') :
    IsFinite (spMap (IntermediateField.inclusion h).toRingHom) ∧
      Surjective (spMap (IntermediateField.inclusion h).toRingHom) := by
  have hq : (algebraMap ℚ F').Finite := RingHom.finite_algebraMap.2 inferInstance
  have he : algebraMap ℚ F' = (IntermediateField.inclusion h).toRingHom.comp (algebraMap ℚ F) := Subsingleton.elim _ _
  rw [he] at hq
  refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_comp_finite hq), ⟨fun x => ?_⟩⟩
  refine ⟨closedPoint F', Subsingleton.elim _ _⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_rankZero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : Dw.p + Dw.q = 0) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  have hz := (GlobalTheory.Models.RankZero.isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo).2
  refine ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, RingHom.id _, ⟨hV, hB.1.2.2.2, hB.2⟩,
    Function.injective_id, inferInstance, RingHom.Finite.id V, fun a => rfl, Inhab.zeroTriple H _,
    Inhab.zeroTriple H _, GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _)
      (GlobalTheory.Models.RankZero.isIso_zeroTriple _) _,
    GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _) hz _⟩

theorem exists_pos {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  haveI := c.fin
  obtain ⟨l₂, hdvd, -, hgood⟩ := GlobalTheory.GoodMultipleLevel.exists_good_multiple E H l
  obtain ⟨c₂, hle⟩ := GlobalTheory.TupleCover.exists_coeff_ge l₂ c.F
  haveI := c₂.fin
  let Xf : ∀ l' : Geo.Tor.Level H, Moduli Dw l' := fun l' => (GlobalTheory.moduliScheme_levelMaps_heckePoints.1 E H Dw l' hD).some
  obtain ⟨s, hs⟩ := GlobalTheory.GlobalAllLevels.exists_sys_global_models E H Dw hD Xf
  obtain ⟨Ygl, -⟩ := hs l₂ c₂ hgood
  obtain ⟨r, h, r₀, m, hr, hfin, -, hsurj⟩ :=
    GlobalTheory.LevelMapBase.levelMap_coeff_le E H Dw l l₂ Xo (Xf l₂) c c₂ hle hD hdvd
  obtain ⟨hF, hS⟩ := finite_surjective_spMap hle
  have hrl : pullback.lift r _ h ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  haveI : IsFinite r := hrl ▸ inferInstance
  have hrs : Surjective r := hrl ▸ inferInstance
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point' r (FractionRing V) y (hrs.surj _)
  haveI : IsAdicComplete (maximalIdeal V) V := hB.1.2.2.2
  haveI : CharZero V := hB.2
  obtain ⟨V₁, _, _, _, j, e, hB₁, hD₁, hj, hjl, hjf, he⟩ := exists_closure_finite V L
  obtain ⟨t, tK, ⟨mK⟩, ⟨mx⟩⟩ := exists_genOf_of_model Ygl V₁ (spMap e ≫ η)
  obtain ⟨mx', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m mx
  have key : ((spMap e ≫ η) ≫ pullback.fst _ _) ≫ r₀ =
      (spMap (e.comp (algebraMap (FractionRing V) L)) ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, ← hr, ← Category.assoc η, hη, ← spMap_comp'']
    simp only [Category.assoc]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, j, e.comp (algebraMap (FractionRing V) L),
    ⟨hD₁, hB₁.1.2.2.2, hB₁.2⟩, hj, hjl, hjf, fun a => he a, t, tK, ⟨mK⟩, ⟨?_⟩⟩
  rw [key] at mx'
  exact mx'

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_ext_semi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hB hV y
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · exact exists_rankZero H Dw hD l Xo c V hB hV y
  · exact exists_pos H Dw hD l Xo c V hB hV y

end GlobalTheory.TraitSemi
