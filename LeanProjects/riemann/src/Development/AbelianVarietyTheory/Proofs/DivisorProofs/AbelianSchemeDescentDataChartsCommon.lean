import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteRegularLocalMeetOfFlatMapsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.CommonChart

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spinj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem flat_generic {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) [Flat φ] :
    φ (genericPoint Y) = genericPoint X := by
  have hg : GeneralizingMap φ := Flat.generalizingMap φ
  obtain ⟨y, hy, e⟩ := hg (genericPoint_specializes (φ (genericPoint Y)))
  have : y = genericPoint Y := (hy.antisymm (genericPoint_specializes y)).eq
  rw [← this, e]

theorem exists_ff {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) [Flat φ] :
    ∃ θ : X.functionField →+* Y.functionField, gp Y ≫ φ = spMap θ ≫ gp X := by
  have h := flat_generic φ
  refine ⟨((X.presheaf.stalkSpecializes (specializes_of_eq h)) ≫ φ.stalkMap (genericPoint Y)).hom, ?_⟩
  show Y.fromSpecStalk _ ≫ φ = Spec.map (_ ≫ _) ≫ X.fromSpecStalk _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem gp_spec (R : CommRingCat.{0}) [IsDomain R] :
    ∃ c : R →+* (Spec R).functionField, Function.Injective c ∧ gp (Spec R) = spMap c :=
  ⟨algebraMap R (Spec R).functionField, IsFractionRing.injective R (Spec R).functionField,
    Spec.fromSpecStalk_eq' _ _⟩

theorem gp_factor {E : Type} [CommRing E] [IsDomain E] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp E) [Flat p] :
    ∃ t : Sp Y.functionField ⟶ Sp (FractionRing E), t ≫ jK E = gp Y ≫ p := by
  obtain ⟨θ, h⟩ := exists_ff p
  obtain ⟨c, hc, this⟩ := gp_spec (CommRingCat.of E)
  have hi : Function.Injective (θ.comp c) := θ.injective.comp hc
  refine ⟨spMap (IsFractionRing.lift hi), ?_⟩
  rw [h, spc]
  rw [this, spc]
  congr 1
  ext z
  simp

theorem ring_part (R R₀ R' O Ω : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] [IsRegularLocalRing R₀]
    [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing O] [IsLocalRing O] [Field Ω]
    [Algebra R O] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime O p]
    (ρ : R →+* R₀) (hρ : ρ.Flat) (φ' : O →+* R') [IsLocalHom φ'] (u : R₀ →+* Ω) (u' : R' →+* Ω)
    (hc : IsAdicComplete (maximalIdeal R') R') (he : IsEtaleCompletion φ')
    (hu : ((residue R').comp φ').FormallyUnramified) (hk : RingHom.ker u' = maximalIdeal R')
    (huu : u.comp ρ = u'.comp (φ'.comp (algebraMap R O))) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₀ →+* E) (b : R' →+* E)
      (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp ρ = b.comp (φ'.comp (algebraMap R O)) ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (RingHom.ker u).map a = maximalIdeal E := by
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing p.primeCompl O inferInstance
  haveI hq : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
  let R₁ := Localization.AtPrime (RingHom.ker u)
  haveI : IsRegularRing R₀ := isRegularRing_of_isRegularLocalRing R₀
  haveI : IsRegularLocalRing R₁ := IsRegularRing.isRegularLocalRing_localization _
  have h1 : ∀ s : p.primeCompl, IsUnit (((algebraMap R₀ R₁).comp ρ) s) := by
    intro s
    have hs : IsUnit (u (ρ s)) := by
      have := RingHom.congr_fun huu s
      simp only [RingHom.comp_apply] at this
      rw [this]
      exact ((IsLocalization.map_units O s).map φ').map u'
    exact IsLocalization.map_units R₁ (⟨ρ s, fun h => hs.ne_zero h⟩ : (RingHom.ker u).primeCompl)
  have h2 : ∀ s : (RingHom.ker u).primeCompl, IsUnit (u s) := fun s => Ne.isUnit s.2
  let φ₁ : O →+* R₁ := IsLocalization.lift h1
  let u₁ : R₁ →+* Ω := IsLocalization.lift h2
  have e1 : φ₁.comp (algebraMap R O) = (algebraMap R₀ R₁).comp ρ := IsLocalization.lift_comp h1
  have e2 : u₁.comp (algebraMap R₀ R₁) = u := IsLocalization.lift_comp h2
  have hm : (RingHom.ker u).map (algebraMap R₀ R₁) = maximalIdeal R₁ := Localization.AtPrime.map_eq_maximalIdeal
  have k1 : RingHom.ker u₁ = maximalIdeal R₁ := by
    refine ((maximalIdeal.isMaximal R₁).eq_of_le (RingHom.ker_ne_top u₁) ?_).symm
    rw [← hm, Ideal.map_le_iff_le_comap, RingHom.comap_ker, e2]
  have e3 : u₁.comp φ₁ = u'.comp φ' := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [RingHom.comp_assoc, e1, ← RingHom.comp_assoc, e2, huu]; rfl
  have fl0 : (algebraMap R₀ R₁).Flat := by
    rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat R₁ (RingHom.ker u).primeCompl
  have fl1 : φ₁.Flat := by
    have hf : (φ₁.comp (algebraMap R O)).Flat := by rw [e1]; exact hρ.comp fl0
    letI : Algebra O R₁ := φ₁.toAlgebra
    letI : Algebra R R₁ := (φ₁.comp (algebraMap R O)).toAlgebra
    haveI : IsScalarTower R O R₁ := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Module.Flat R R₁ := hf
    exact (Module.flat_iff_of_isLocalization O p.primeCompl R₁).mpr this
  have lo : IsLocalHom φ₁ := by
    refine ⟨fun z hz => ?_⟩
    have : u' (φ' z) ≠ 0 := by
      have h := RingHom.congr_fun e3 z
      simp only [RingHom.comp_apply] at h
      rw [← h]; exact (hz.map u₁).ne_zero
    apply isUnit_of_map_unit φ'
    by_contra hn
    exact this (by rw [← RingHom.mem_ker, hk]; exact hn)
  obtain ⟨E, _, _, _, a, b, v, fa, fb, hab, hv, hva, hvb, hma, -⟩ :=
    GlobalTheory.T.exists_complete_regular_local_meet_of_flat_maps O R₁ R' Ω φ₁ φ' u₁ u' fl1 lo hc he hu k1 hk e3
  refine ⟨E, _, inferInstance, inferInstance, a.comp (algebraMap R₀ R₁), b, v, fl0.comp fa, fb, ?_, hv, ?_, hvb, ?_⟩
  · rw [RingHom.comp_assoc, ← e1, ← RingHom.comp_assoc, hab]; rfl
  · rw [← RingHom.comp_assoc, hva, e2]
  · rw [← Ideal.map_map, hm, hma]

theorem gen_part {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x)
    {E : Type} [CommRing E] [IsDomain E] (a : C.R →+* E) (ha : a.Flat) :
    ∃ (y : Sp (FractionRing E) ⟶ X)
      (l : ((Over.pullback (jK E)).obj ((Over.pullback (spMap a)).obj C.G)).left ⟶ pullback C.G.hom (jK C.R)),
      y ≫ j = jK E ≫ spMap a ≫ C.ξ ∧
      l ≫ pullback.fst _ _ = pullback.fst ((Over.pullback (spMap a)).obj C.G).hom (jK E) ≫ pullback.fst C.G.hom (spMap a) ∧
      IsGrpPullback ((Over.pullback (jK E)).obj ((Over.pullback (spMap a)).obj C.G)) A y (l ≫ C.α) := by
  have hi : Function.Injective a := by
    letI : Algebra C.R E := a.toAlgebra
    haveI : Module.Flat C.R E := ha
    exact FaithfulSMul.algebraMap_injective C.R E
  have hi' : Function.Injective ((algebraMap E (FractionRing E)).comp a) :=
    (IsFractionRing.injective E (FractionRing E)).comp hi
  let aK : FractionRing C.R →+* FractionRing E := IsFractionRing.lift hi'
  have e : jK E ≫ spMap a = spMap aK ≫ jK C.R := by
    rw [spc, spc]
    congr 1
    ext z
    simp [aK]
  have p := ((isGrpPullback_pullback ((Over.pullback (spMap a)).obj C.G) (jK E)).comp
    (isGrpPullback_pullback C.G (spMap a))).congr e rfl
  have q := isGrpPullback_pullback C.G (jK C.R)
  have w := p.1.w
  rw [← Category.assoc] at w
  refine ⟨spMap aK ≫ C.y, q.1.lift _ _ w, ?_, q.1.lift_fst _ _ w, ?_⟩
  · rw [Category.assoc, C.hy, ← Category.assoc, ← e, Category.assoc]
  · exact (IsGrpPullback.cancel q (p.congr rfl (q.1.lift_fst _ _ w).symm) (q.1.lift_snd _ _ w)).comp C.gen

theorem iso_extend {E : Type} [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E]
    (G H : Over (Sp E)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (jK E)).obj G ≅ (Over.pullback (jK E)).obj H) [IsMonHom e.hom] :
    ∃ F : G ≅ H, IsMonHom F.hom ∧ (Over.pullback (jK E)).map F.hom = e.hom := by
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelian_hom_extend_generic E G H hG hH e.hom inferInstance
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := semiAbelian_hom_extend_generic E H G hH hG e.inv inferInstance
  refine ⟨⟨F, F', ?_, ?_⟩, hF, eF⟩
  · exact (semiAbelian_hom_extend_generic E G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, eF, eF', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (semiAbelian_hom_extend_generic E H H hH hH (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, eF, eF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ring_setup (σ : Setup) (x x' : Sp σ.R) (Ω : Type) [Field Ω] (u : (σ.C x).R →+* Ω) (u' : (σ.C x').R →+* Ω)
    (hk : RingHom.ker u' = maximalIdeal _) (huu : u.comp (σ.ρ x) = u'.comp (σ.ρ x')) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : (σ.C x).R →+* E)
      (b : (σ.C x').R →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp (σ.ρ x) = b.comp (σ.ρ x') ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (RingHom.ker u).map a = maximalIdeal E := by
  let z : Sp σ.R := (σ.C x').ξ (closedPoint (σ.C x').R)
  haveI : z.asIdeal.IsPrime := z.isPrime
  letI : Algebra σ.R ((Sp σ.R).presheaf.stalk z) := (StructureSheaf.toStalk σ.R z).hom.toAlgebra
  haveI : IsLocalization.AtPrime ((Sp σ.R).presheaf.stalk z) z.asIdeal := StructureSheaf.IsLocalization.to_stalk σ.R z
  have e : (Scheme.stalkClosedPointTo (σ.C x').ξ).hom.comp (algebraMap σ.R ((Sp σ.R).presheaf.stalk z)) = σ.ρ x' := by
    apply spinj
    rw [← spc, ← σ.hρ x']
    have h := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (σ.C x').ξ
    rw [Spec.fromSpecStalk_eq'] at h
    exact h
  have := ring_part σ.R (σ.C x).R (σ.C x').R ((Sp σ.R).presheaf.stalk z) Ω z.asIdeal (σ.ρ x) (σ.flat x)
    (Scheme.stalkClosedPointTo (σ.C x').ξ).hom u u' (σ.C x').complete (σ.C x').etc (σ.C x').unr hk (by rw [e, huu])
  rwa [e] at this

theorem ff_eq (σ : Setup) (x : Sp σ.R) {K : Type} [Field K] (θ : (σ.C x).G.left.functionField →+* K)
    (t : Sp K ⟶ pullback (σ.C x).G.hom (jK (σ.C x).R)) (ht : t ≫ pullback.fst _ _ = spMap θ ≫ gp (σ.C x).G.left) :
    t ≫ (σ.C x).α = spMap (θ.comp (σ.θ x)) ≫ gp σ.A.left := by
  obtain ⟨l, h₁, h₂⟩ := σ.hθ x
  rw [σ.compat x _ t (spMap θ ≫ l) (by rw [ht, Category.assoc, h₁]), Category.assoc, h₂, ← Category.assoc, spc]

end GlobalTheory.Desc.CommonChart

namespace GlobalTheory.Desc
open CommonChart

theorem setup_common : ∀ σ : Setup, σ.Common := by
  intro σ x x' Ω _ u u' hk huu
  obtain ⟨E, _, _, _, a, b, v, fa, fb, hab, hv, hva, hvb, hma⟩ := ring_setup σ x x' Ω u u' hk huu
  haveI : IsIntegrallyClosed E := (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing E).2
  obtain ⟨ya, la, hya, hla, pa⟩ := gen_part (σ.C x) a fa
  obtain ⟨yb, lb, hyb, hlb, pb⟩ := gen_part (σ.C x') b fb
  have hy : yb = ya := by
    rw [← cancel_mono (awayMap σ.f), hya, hyb, σ.hρ, σ.hρ, spc _ a, spc _ b, hab]
  subst hy
  obtain ⟨e, he, hee⟩ := grpPullback_iso pa pb
  have sa := IsSemiAbelian.pullback (spMap a) _ (σ.C x).semi
  have sb := IsSemiAbelian.pullback (spMap b) _ (σ.C x').semi
  obtain ⟨F, hF, eF⟩ := iso_extend _ _ sa sb e
  haveI := sa
  haveI : IsIntegral ((Over.pullback (spMap a)).obj (σ.C x).G).left := isIntegral_left_of_isSemiAbelian _
  have ga := isGrpPullback_pullback (σ.C x).G (spMap a)
  have gb := ((isGrpPullback_of_iso F).comp (isGrpPullback_pullback (σ.C x').G (spMap b))).congr
    (Category.id_comp _) rfl
  haveI : Flat (spMap a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact fa
  haveI : Flat (spMap b) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact fb
  haveI : Flat (pullback.fst (σ.C x).G.hom (spMap a)) := inferInstance
  haveI : Flat (F.hom.left ≫ pullback.fst (σ.C x').G.hom (spMap b)) :=
    MorphismProperty.of_isPullback (P := @Flat) gb.1.flip inferInstance
  obtain ⟨θa, ha⟩ := @exists_ff _ ((Over.pullback (spMap a)).obj (σ.C x).G).left _ _
    (pullback.fst (σ.C x).G.hom (spMap a)) inferInstance
  obtain ⟨θb, hb⟩ := exists_ff (F.hom.left ≫ pullback.fst (σ.C x').G.hom (spMap b))
  refine ⟨E, _, inferInstance, inferInstance, a, b, v, (Over.pullback (spMap a)).obj (σ.C x).G, inferInstance,
    inferInstance, _, _, θa, θb, fa, fb, hab, hv, hva, hvb, hma, sa, ga, gb,
    ⟨_, Category.comp_id _, ha⟩, ⟨_, Category.comp_id _, hb⟩, ?_⟩
  haveI := sa.smooth
  obtain ⟨t, ht⟩ := gp_factor ((Over.pullback (spMap a)).obj (σ.C x).G).hom
  let m := pullback.lift _ _ ht.symm
  have hm : m ≫ pullback.fst _ _ = gp _ := pullback.lift_fst _ _ _
  have e₁ := ff_eq σ x θa (m ≫ la) (by rw [Category.assoc, hla, ← Category.assoc, hm, ha])
  have hE : e.hom.left ≫ pullback.fst ((Over.pullback (spMap b)).obj (σ.C x').G).hom (jK E) =
      pullback.fst ((Over.pullback (spMap a)).obj (σ.C x).G).hom (jK E) ≫ F.hom.left := by
    rw [← eF]; exact pullback.lift_fst _ _ _
  have e₂ := ff_eq σ x' θb (m ≫ e.hom.left ≫ lb) (by
    rw [Category.assoc, Category.assoc, hlb, reassoc_of% hE, ← Category.assoc, hm, hb])
  haveI : Mono (gp σ.A.left) := by unfold gp; infer_instance
  apply spinj
  rw [← cancel_mono (gp σ.A.left), ← e₁, ← e₂, Category.assoc, Category.assoc, Category.assoc, hee]

end GlobalTheory.Desc
