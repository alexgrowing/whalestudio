import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleDiv

open IsLocalRing

theorem formallyEtale_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

theorem formallyEtale_of_comp_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective g) (h : (g.comp f).FormallyEtale) :
    f.FormallyEtale := by
  let e := RingEquiv.ofBijective g hg
  have : f = (e.symm : T →+* S).comp (g.comp f) := by
    ext x
    exact (e.symm_apply_apply (f x)).symm
  rw [this]
  exact h.comp (formallyEtale_of_bijective _ e.symm.bijective)

theorem formallyEtale_stalkMap {M W : Scheme.{0}} (f : M ⟶ W) (U : M.Opens)
    [Etale (U.ι ≫ f)] (w : U.toScheme) : (f.stalkMap (U.ι w)).hom.FormallyEtale := by
  have hu := FormallyUnramified.stalkMap (U.ι ≫ f) w
  have hs : ((U.ι ≫ f).stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ w))
  have h : ((U.ι ≫ f).stalkMap w).hom.FormallyEtale := by
    algebraize [((U.ι ≫ f).stalkMap w).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have : IsIso (U.ι.stalkMap w) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h
  exact formallyEtale_of_comp_bijective (f.stalkMap (U.ι w)).hom (U.ι.stalkMap w).hom
    (ConcreteCategory.bijective_of_isIso _) h

theorem strictMono_ι {M : Scheme.{0}} (U : M.Opens) : StrictMono U.ι := by
  have hi := U.ι.isOpenEmbedding.isInducing
  intro a b h
  refine lt_of_le_not_ge ?_ ?_
  · exact hi.specializes_iff.2 h.le
  · exact fun h' => h.not_ge (hi.specializes_iff.1 h')

theorem map_maximalIdeal_stalk {M W : Scheme.{0}} (f : M ⟶ W) [LocallyOfFiniteType f] (z : M)
    (h : (f.stalkMap z).hom.FormallyEtale) :
    (maximalIdeal (W.presheaf.stalk (f z))).map (f.stalkMap z).hom =
      maximalIdeal (M.presheaf.stalk z) := by
  have hft := LocallyOfFiniteType.stalkMap f z
  algebraize [(f.stalkMap z).hom]
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f z)) (M.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem log_ordFrac_map {K L : Type} [Field K] [Field L] (V : ValuationSubring K)
    (V' : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing V']
    (ρ : K →+* L) (ψ : V →+* V') (hψ : ∀ a, (ψ a : L) = ρ a) {t : V} (ht : Irreducible t)
    (ht' : Irreducible (ψ t)) {g : K} (hg : g ≠ 0) :
    WithZero.log (Ring.ordFrac V' (ρ g)) = WithZero.log (Ring.ordFrac V g) := by
  obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_zpow (F := K) ht hg
  have h1 := ordTop_vw_unit_mul_zpow (F := K) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := L) ht' (Units.map ψ.toMonoidHom u) m
  have e : ρ (algebraMap V K u * algebraMap V K t ^ m) =
      algebraMap V' L (Units.map ψ.toMonoidHom u) * algebraMap V' L (ψ t) ^ m := by
    rw [map_mul, map_zpow₀]
    simp [hψ]
  rw [← e] at h2
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_inj] at h1
  rw [ordTop_vw_of_ne_zero _ ((map_ne_zero ρ).2 hg), WithTop.coe_inj] at h2
  rw [h1, h2]

theorem isFreeGen_formMap {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {D : ℕ}
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem maximalIdeal_eq_bot {X : Scheme.{0}} [IsIntegral X] {x : X} (h : Order.coheight x = 0) :
    maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h.le
  exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime ⊥).symm

theorem coheight_apply_eq_one {M W : Scheme.{0}} [IsIntegral W] (f : M ⟶ W) [LocallyOfFiniteType f]
    (U : M.Opens) [Etale (U.ι ≫ f)] (w : U.toScheme) (h1 : Order.coheight (U.ι w) = 1)
    (hB : maximalIdeal (M.presheaf.stalk (U.ι w)) ≠ ⊥) : Order.coheight (f (U.ι w)) = 1 := by
  have hle : Order.coheight w ≤ 1 :=
    h1 ▸ Order.coheight_le_coheight_apply_of_strictMono _ (strictMono_ι U) w
  have hle' := GlobalTheory.GenExtendNormal.coheight_apply_le_one (U.ι ≫ f) (Flat.generalizingMap _) w hle
  refine le_antisymm hle' ?_
  rw [Order.one_le_iff_ne_zero]
  intro h0
  apply hB
  rw [← map_maximalIdeal_stalk f _ (formallyEtale_stalkMap f U w), maximalIdeal_eq_bot h0,
    Ideal.map_bot]

theorem exists_isAt_ord_formOrd : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f]
    (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z →
    ∃ E : DivOver p, E.IsAt (f z) ∧
      (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  intro M W _ _ _ _ p f _ n _ _ U hU z hz E' hE'
  haveI := hU
  obtain ⟨w, rfl⟩ : ∃ w : U.toScheme, U.ι w = z := ⟨⟨z, hz⟩, rfl⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := GlobalTheory.ModifSections.isNormalScheme_of_smooth p
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  haveI hB : IsDiscreteValuationRing (M.presheaf.stalk (U.ι w)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing hE'.equiv.symm
  have hφ := formallyEtale_stalkMap f U w
  have hmax := map_maximalIdeal_stalk f (U.ι w) hφ
  have hc := coheight_apply_eq_one f U w hE'.coheight_eq_one
    (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
  haveI hA : IsDiscreteValuationRing (W.presheaf.stalk (f (U.ι w))) :=
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hc
  let ψ : E.ring →+* E'.ring :=
    hE'.equiv.toRingHom.comp ((f.stalkMap (U.ι w)).hom.comp hE.equiv.symm.toRingHom)
  have hψ : ∀ a, (ψ a : M.functionField) = functionFieldMap f a := by
    intro a
    obtain ⟨b, rfl⟩ := hE.equiv.surjective a
    have e : ψ (hE.equiv b) = hE'.equiv (f.stalkMap (U.ι w) b) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact (functionFieldMap_algebraMap f (U.ι w) b).symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (W.presheaf.stalk (f (U.ι w)))
  have ht' : Irreducible (f.stalkMap (U.ι w) t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at ht ⊢
    rw [← hmax, ht, Ideal.map_span, Set.image_singleton]
  have htE : Irreducible (hE.equiv t) := ht.map hE.equiv
  have htE' : Irreducible (ψ (hE.equiv t)) := by
    have e : ψ (hE.equiv t) = hE'.equiv (f.stalkMap (U.ι w) t) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact ht'.map hE'.equiv
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    log_ordFrac_map E.ring E'.ring (functionFieldMap f) ψ hψ htE htE' g.ne_zero
  refine ⟨E, hE, hord, fun η hη => ?_⟩
  have hn : topologicalKrullDim W = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨c, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have hconst : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext
    ((hψ _).trans (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a))
  have hψFE : ψ.FormallyEtale :=
    RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp
      (formallyEtale_of_bijective _ hE.equiv.symm.bijective) hφ)
      (formallyEtale_of_bijective _ hE'.equiv.bijective)
  have h3 : ((functionFieldMap f).comp E.ring.subtype).comp E.const = Cartier.constFn (f ≫ p) := by
    ext a
    exact RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a
  have e1 : GlobalTheory.EtaleKlt.ratPull p f n (E.toRat n ω) =
      E'.toRat n (TopForm.formMap n ψ hconst ω) := by
    change TopForm.formMap n (functionFieldMap f) _ (TopForm.formMap n E.ring.subtype rfl ω) =
      TopForm.formMap n E'.ring.subtype rfl (TopForm.formMap n ψ hconst ω)
    exact (formMap_formMap E.ring.subtype (functionFieldMap f)
      ((functionFieldMap f).comp E.ring.subtype) rfl _ _ h3 ω).trans
      (formMap_formMap ψ E'.ring.subtype ((functionFieldMap f).comp E.ring.subtype)
        (RingHom.ext hψ) _ _ h3 ω).symm
  have h1 : E.formOrd (c • E.toRat n ω) = E.ord (Units.mk0 c hc0) :=
    DivOver.IsFormOrd.formOrd_eq hη ⟨ω, hω, Units.mk0 c hc0, rfl, rfl⟩
  have hη' : GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω) ≠ 0 := by
    have hfree := E'.isFreeGen_toRat (isFreeGen_formMap hψFE hconst hω)
    rw [map_smulₛₗ, e1]
    intro h0
    have := hfree.1 (a₁ := functionFieldMap f c) (a₂ := 0) (by simp only [h0, zero_smul])
    exact hc0 ((map_eq_zero _).1 this)
  have h2 : E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
      E'.ord (Units.map (functionFieldMap f).toMonoidHom (Units.mk0 c hc0)) :=
    DivOver.IsFormOrd.formOrd_eq hη' ⟨_, isFreeGen_formMap hψFE hconst hω, _,
      by rw [map_smulₛₗ, e1]; rfl, rfl⟩
  rw [h1, h2, hord]

end GlobalTheory.EtaleDiv
