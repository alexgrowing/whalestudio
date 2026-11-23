import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import GroundTheory.FunctionField.PlaceDefs
set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology

open scoped WithZero

universe u

namespace GroundTheory.Arith.SchemeCoh

section Valuation

theorem valuation_eq_of_isEquiv {K : Type*} [Field K] {v w : Valuation K ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  have disc : ∀ x : ℤᵐ⁰, x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]
    omega
  have lt1 : ∀ x, v x < 1 ↔ w x < 1 := fun x => by
    have h1 := h 1 x
    simp only [map_one] at h1
    rw [← not_le, ← not_le, h1]
  have eq1 : ∀ x, v x = 1 ↔ w x = 1 := fun x => by
    have h1 := h 1 x
    have h2 := h x 1
    simp only [map_one] at h1 h2
    rw [le_antisymm_iff, le_antisymm_iff, h1, h2]
  obtain ⟨π, hπ⟩ := hw (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := hv (WithZero.exp (-1))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hvπ : v π = WithZero.exp (-1) := by
    refine le_antisymm ?_ ?_
    · exact disc _ ((Valuation.ne_zero_iff _).mpr hπ0) ((lt1 π).mpr (hπ ▸ hexp))
    · rw [← hϖ]
      refine (h ϖ π).mpr ?_
      rw [hπ]
      exact disc _ ((Valuation.ne_zero_iff _).mpr hϖ0) ((lt1 ϖ).mp (hϖ ▸ hexp))
  ext f
  by_cases hf : f = 0
  · simp [hf]
  have hwf : w f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  set n := WithZero.log (w f) with hn
  have hwf' : w f = WithZero.exp n := (WithZero.exp_log hwf).symm
  have hpow : ∀ u : Valuation K ℤᵐ⁰, u π = WithZero.exp (-1) →
      u (f * π ^ n) = u f * WithZero.exp (-n) := by
    intro u hu
    rw [map_mul, map_zpow₀, hu, ← WithZero.exp_zsmul]
    simp
  have hg : w (f * π ^ n) = 1 := by
    rw [hpow w hπ, hwf', ← WithZero.exp_add]
    simp
  have hg' := (eq1 _).mpr hg
  rw [hpow v hvπ] at hg'
  rw [hwf']
  have : v f = v f * WithZero.exp (-n) * WithZero.exp n := by
    rw [mul_assoc, ← WithZero.exp_add]
    simp
  rw [this, hg', one_mul]

end Valuation

section ToPlace

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor

lemma valuation_surjective (Z : PrimeDivisor X) : Function.Surjective Z.valuation := by
  have := Z.isDedekindDomain_stalk
  exact IsDedekindDomain.HeightOneSpectrum.valuation_surjective _ _

lemma valuation_le_one_iff (Z : PrimeDivisor X) (f : X.functionField) :
    Z.valuation f ≤ 1 ↔ f ∈ (algebraMap (X.presheaf.stalk Z.point) X.functionField).range := by
  by_cases hf : f = 0
  · subst hf
    simp only [map_zero, zero_le, true_iff]
    exact ⟨0, map_zero _⟩
  rw [← Z.ord_nonneg_iff hf, ← WithZero.exp_zero, Z.valuation_le_exp_iff hf, neg_zero]

noncomputable def toPlace (Z : PrimeDivisor X) : Place k X.functionField where
  ring := Z.valuation.valuationSubring
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := Z.valuation_surjective (WithZero.exp 1)
    have hmem : π ∈ Z.valuation.valuationSubring := htop ▸ trivial
    rw [Valuation.mem_valuationSubring_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (X.presheaf.stalk Z.point) X.functionField]
    exact Z.valuation_algebraMap_le_one _

lemma mem_toPlace_ring (Z : PrimeDivisor X) (f : X.functionField) :
    f ∈ (Z.toPlace (k := k)).ring ↔ Z.valuation f ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

variable [IsFunctionField k X.functionField]

theorem toPlace_valuation (Z : PrimeDivisor X) : (Z.toPlace (k := k)).valuation = Z.valuation := by
  refine valuation_eq_of_isEquiv (Place.valuation_surjective _) Z.valuation_surjective ?_
  refine Valuation.isEquiv_of_val_le_one fun f => ?_
  rw [Place.valuation_le_one_iff, mem_toPlace_ring]

end PrimeDivisor

end ToPlace

section Center

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

lemma fromSpecStalk_genericPoint_comp :
    X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv, ← Scheme.ΓSpecIso_inv_naturality]
  have h1 : (homOfLE le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ⟶ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h1, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

variable (R : ValuationSubring X.functionField)

noncomputable def centerMorphism {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R) :
    Spec (.of R) ⟶ X :=
  Spec.map φ ≫ X.fromSpecStalk x

lemma specMap_comp_centerMorphism {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R)
    (hφ : ∀ a, ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a) :
    Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ centerMorphism R φ =
      X.fromSpecStalk (genericPoint X) := by
  unfold centerMorphism
  rw [← Category.assoc, ← Spec.map_comp]
  have h : φ ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      X.presheaf.stalkSpecializes (genericPoint_specializes x) := by
    ext a
    exact hφ a
  rw [h, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

lemma centerMorphism_closedPoint {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R)
    [IsLocalHom φ.hom] : centerMorphism R φ (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x (Spec.map φ (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

omit [IsIntegral X] in

lemma eq_of_specMap_comp_eq {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]
    (hι : Function.Injective (algebraMap A K)) {g₁ g₂ : Spec (.of A) ⟶ Spec (.of k)}
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₁ =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₂) : g₁ = g₂ := by
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext a
  have h' := congr($h a)
  exact hι h'

theorem center_unique [IsSeparated (X ↘ Spec (.of k))] {x y : X}
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of R) (ψ : X.presheaf.stalk y ⟶ CommRingCat.of R)
    [IsLocalHom φ.hom] [IsLocalHom ψ.hom]
    (hφ : ∀ a, ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a)
    (hψ : ∀ a, ((ψ a : R) : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a) :
    x = y := by
  let S : ValuativeCommSq (X ↘ Spec (.of k)) :=
    { R := R, K := X.functionField, i₁ := X.fromSpecStalk (genericPoint X),
      i₂ := centerMorphism R φ ≫ (X ↘ Spec (.of k)),
      commSq := ⟨by rw [← specMap_comp_centerMorphism R φ hφ, Category.assoc]⟩ }
  have hU := IsSeparated.valuativeCriterion (X ↘ Spec (.of k)) S
  let l₁ : S.commSq.LiftStruct :=
    { l := centerMorphism R φ, fac_left := specMap_comp_centerMorphism R φ hφ, fac_right := rfl }
  let l₂ : S.commSq.LiftStruct :=
    { l := centerMorphism R ψ, fac_left := specMap_comp_centerMorphism R ψ hψ,
      fac_right := by
        refine eq_of_specMap_comp_eq (A := R) (K := X.functionField) Subtype.val_injective ?_
        change _ ≫ centerMorphism R ψ ≫ _ = _ ≫ centerMorphism R φ ≫ _
        rw [← Category.assoc, ← Category.assoc, specMap_comp_centerMorphism R ψ hψ,
          specMap_comp_centerMorphism R φ hφ] }
  have h := congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  rw [← centerMorphism_closedPoint R φ, ← centerMorphism_closedPoint R ψ]
  exact congrArg (fun g : Spec (.of R) ⟶ X => g (IsLocalRing.closedPoint R)) h

lemma compatible_of_specMap_comp {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ centerMorphism R φ =
      X.fromSpecStalk (genericPoint X)) (a : X.presheaf.stalk x) :
    ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a := by
  unfold centerMorphism at h
  rw [← Category.assoc, ← Spec.map_comp,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x),
    cancel_mono, Spec.map_inj] at h
  exact congr($h a)

theorem exists_center [UniversallyClosed (X ↘ Spec (.of k))]
    (hR : ∀ c : k, algebraMap k X.functionField c ∈ R) :
    ∃ (x : X) (φ : X.presheaf.stalk x ⟶ CommRingCat.of R), IsLocalHom φ.hom ∧
      ∀ a, ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a := by
  have hE : ValuativeCriterion.Existence (X ↘ Spec (.of k)) := by
    have h := ‹UniversallyClosed (X ↘ Spec (.of k))›
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let ρ : k →+* R := (algebraMap k X.functionField).codRestrict R hR
  let S : ValuativeCommSq (X ↘ Spec (.of k)) :=
    { R := R, K := X.functionField, i₁ := X.fromSpecStalk (genericPoint X),
      i₂ := Spec.map (CommRingCat.ofHom ρ),
      commSq := ⟨by rw [fromSpecStalk_genericPoint_comp, ← Spec.map_comp]; rfl⟩ }
  obtain ⟨l, hl₁, -⟩ := (hE S).exists_lift
  refine ⟨l (IsLocalRing.closedPoint R), Scheme.stalkClosedPointTo l, inferInstance, ?_⟩
  refine compatible_of_specMap_comp R _ ?_
  unfold centerMorphism
  rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact hl₁

end Center

section PlaceEquiv

open GroundTheory.FunctionField

theorem valuationSubring_eq_of_le {K : Type*} [Field K] {A B : ValuationSubring K} (hAB : A ≤ B)
    (hloc : ∀ a ∈ A, a⁻¹ ∈ B → a⁻¹ ∈ A) : A = B := by
  refine le_antisymm hAB fun b hb => ?_
  by_contra hbA
  have hinv : b⁻¹ ∈ A := (A.mem_or_inv_mem b).resolve_left hbA
  have := hloc _ hinv (by rwa [inv_inv])
  rw [inv_inv] at this
  exact hbA this

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor

noncomputable def stalkToPlaceRing (Z : PrimeDivisor X) :
    X.presheaf.stalk Z.point ⟶ CommRingCat.of (Z.toPlace (k := k)).ring :=
  CommRingCat.ofHom ((algebraMap (X.presheaf.stalk Z.point) X.functionField).codRestrict
    (Z.toPlace (k := k)).ring fun a => (Z.mem_toPlace_ring _).mpr (Z.valuation_algebraMap_le_one a))

lemma stalkToPlaceRing_apply (Z : PrimeDivisor X) (a : X.presheaf.stalk Z.point) :
    ((Z.stalkToPlaceRing (k := k) a : (Z.toPlace (k := k)).ring) : X.functionField) =
      algebraMap (X.presheaf.stalk Z.point) X.functionField a := rfl

instance (Z : PrimeDivisor X) : IsLocalHom (Z.stalkToPlaceRing (k := k)).hom := by
  refine ⟨fun a ha => ?_⟩
  have := Z.isDedekindDomain_stalk
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hK : algebraMap (X.presheaf.stalk Z.point) X.functionField a * (b : X.functionField) = 1 := by
    rw [← stalkToPlaceRing_apply (k := k)]
    exact congrArg Subtype.val hb
  have hb1 : Z.valuation (b : X.functionField) ≤ 1 := (Z.mem_toPlace_ring _).mp b.2
  have hval : Z.valuation (algebraMap (X.presheaf.stalk Z.point) X.functionField a) = 1 := by
    refine le_antisymm (Z.valuation_algebraMap_le_one a) ?_
    have h1 := congrArg Z.valuation hK
    rw [map_mul, map_one] at h1
    by_contra hlt
    push Not at hlt
    have : Z.valuation (algebraMap (X.presheaf.stalk Z.point) X.functionField a) *
        Z.valuation (b : X.functionField) < 1 :=
      mul_lt_one_of_lt_of_le hlt hb1
    rw [h1] at this
    exact lt_irrefl _ this
  by_contra hnu
  have hm : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.point) :=
    (IsLocalRing.mem_maximalIdeal a).mpr hnu
  have hlt : Z.valuation (algebraMap (X.presheaf.stalk Z.point) X.functionField a) < 1 := by
    simp only [PrimeDivisor.valuation]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hm
  rw [hval] at hlt
  exact lt_irrefl _ hlt

end PrimeDivisor

variable [IsProper (X ↘ Spec (.of k))]

theorem PrimeDivisor.toPlace_injective :
    Function.Injective (PrimeDivisor.toPlace (k := k) (X := X)) := by
  intro Z W h
  have hring : (Z.toPlace (k := k)).ring = (W.toPlace (k := k)).ring := congrArg Place.ring h
  apply PrimeDivisor.point_injective
  let ψ : X.presheaf.stalk W.point ⟶ CommRingCat.of (Z.toPlace (k := k)).ring :=
    W.stalkToPlaceRing (k := k) ≫ CommRingCat.ofHom (RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring hring.symm)).toRingHom
  have : IsLocalHom ψ.hom := by
    dsimp [ψ]
    infer_instance
  exact center_unique (k := k) (Z.toPlace (k := k)).ring (Z.stalkToPlaceRing (k := k)) ψ
    (fun a => rfl) (fun a => rfl)

theorem PrimeDivisor.toPlace_surjective (hX : topologicalKrullDim X ≤ 1) :
    Function.Surjective (PrimeDivisor.toPlace (k := k) (X := X)) := by
  intro v
  obtain ⟨x, φ, hφl, hφ⟩ := exists_center (k := k) v.ring v.algebraMap_mem
  have hx : x ≠ genericPoint X := by
    intro hxη
    apply v.ne_top
    rw [eq_top_iff]
    intro f _
    have hs : x ⤳ genericPoint X := hxη ▸ specializes_rfl
    have h2 : algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.stalkSpecializes hs f) = f := by
      rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
        TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    have h3 := (φ (X.presheaf.stalkSpecializes hs f)).2
    rw [hφ, h2] at h3
    exact h3
  let Z : PrimeDivisor X := ⟨x, ringKrullDim_stalk_eq_one hX hx⟩
  refine ⟨Z, Place.ext ?_⟩
  have hrange : ∀ f : X.functionField, f ∈ (Z.toPlace (k := k)).ring ↔
      f ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := fun f =>
    (Z.mem_toPlace_ring f).trans (Z.valuation_le_one_iff f)
  refine valuationSubring_eq_of_le ?_ ?_
  · intro f hf
    obtain ⟨a, rfl⟩ := (hrange f).mp hf
    rw [← hφ a]
    exact (φ a).2
  · intro f hf hinv
    obtain ⟨a, rfl⟩ := (hrange f).mp hf
    by_cases ha : algebraMap (X.presheaf.stalk x) X.functionField a = 0
    · rw [ha, inv_zero]
      exact zero_mem _
    have hu : IsUnit (φ a) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
      apply Subtype.val_injective
      change ((φ a : v.ring) : X.functionField) * _ = 1
      rw [hφ a]
      exact mul_inv_cancel₀ ha
    have hau : IsUnit a := (isUnit_map_iff φ.hom a).mp hu
    obtain ⟨u, rfl⟩ := hau
    rw [hrange]
    exact ⟨((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x),
      map_units_inv (algebraMap (X.presheaf.stalk x) X.functionField) u⟩

noncomputable def placeEquiv (hX : topologicalKrullDim X ≤ 1) :
    PrimeDivisor X ≃ Place k X.functionField :=
  Equiv.ofBijective PrimeDivisor.toPlace
    ⟨PrimeDivisor.toPlace_injective, PrimeDivisor.toPlace_surjective hX⟩

@[simp]
lemma placeEquiv_apply (hX : topologicalKrullDim X ≤ 1) (Z : PrimeDivisor X) :
    placeEquiv (k := k) hX Z = Z.toPlace := rfl

end PlaceEquiv

end GroundTheory.Arith.SchemeCoh
