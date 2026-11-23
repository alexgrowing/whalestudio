import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.DetHT

namespace GlobalTheory.DetHT.RegLoc

theorem mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (c : Γ(X, U)) :
    x ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    change hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  rwa [hU.fromSpec_primeIdealOf] at h₂

theorem eval_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (κ : Γ(X, U) →+* R) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (((Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec).appLE U ⊤ h) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom s = κ s := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have e1 : (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom κ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have e2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom κ)).appTop =
      CommRingCat.ofHom κ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom κ)).symm
  rw [e1, e2, e3]
  simp

theorem ideal_ne_top {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (hN : IsIntegrallyClosed (X.presheaf.stalk x)) {𝔪 : Ideal Γ(X, U)} (h𝔪 : 𝔪 ≠ ⊤)
    (hP : (hU.primeIdealOf ⟨x, hx⟩).asIdeal ≤ 𝔪) {g : X.functionField} (hg : g ≠ 0) (hreg : ¬ RegAt x g) :
    𝔪.map (algebraMap Γ(X, U) (Algebra.adjoin Γ(X, U) {g⁻¹})) ⊔
      Ideal.span {(⟨g⁻¹, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin Γ(X, U) {g⁻¹})} ≠ ⊤ := by
  intro heq
  letI := invertibleOfNonzero (inv_ne_zero hg)
  obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top g⁻¹ 𝔪 h𝔪 heq
  rw [invOf_eq_inv, inv_inv] at hpx
  have hlc : p.leadingCoeff ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun h =>
    h𝔪 ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (hP h) hp))
  have hu : IsUnit (X.presheaf.germ U x hx p.leadingCoeff) :=
    (X.mem_basicOpen _ _ hx).1 ((mem_basicOpen_iff hU hx _).2 hlc)
  have hgm : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) =
      algebraMap Γ(X, U) X.functionField a := fun a => algebraMap_germ hx a
  let q := p.map (X.presheaf.germ U x hx).hom
  have hq : Polynomial.aeval g q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    convert hpx using 1
    rw [Polynomial.aeval_def]
    congr 1
    ext a
    exact hgm a
  have hlq : q.leadingCoeff = X.presheaf.germ U x hx p.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero
  have hint : IsIntegral (X.presheaf.stalk x) g := by
    refine ⟨Polynomial.C (hu.unit⁻¹ : (X.presheaf.stalk x)ˣ).1 * q,
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlq]; simp), ?_⟩
    rw [← Polynomial.aeval_def, map_mul, hq, mul_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk x) (K := X.functionField)).1 hint
  exact hreg ⟨y, hy⟩

theorem valAt_chart {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {K : Type} [Field K]
    (κ : Γ(X, U) →+* K) (s : Γ(X, U)) :
    RegAt (below (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec)) (algebraMap Γ(X, U) X.functionField s) ∧
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) (algebraMap Γ(X, U) X.functionField s) = κ s := by
  have ht : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ⁻¹ᵁ U := fun x _ =>
    (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩
  have hb : below (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) ∈ U := ht trivial
  refine ⟨⟨_, algebraMap_germ hb s⟩, ?_⟩
  rw [← eval_fromSpec hU κ ht s, ← OfModel.valAt_fnOf _ hb ht]
  rfl

theorem valAt_div {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) {K : Type} [Field K]
    (κ : Γ(X, U) →+* K) (a b : Γ(X, U)) (hb : κ b ≠ 0) {g : X.functionField}
    (hg : g * algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec) g * κ b = κ a := by
  set y : Sp K ⟶ X := Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec with hy
  obtain ⟨⟨b', hb'⟩, hvb⟩ := valAt_chart hU κ b
  obtain ⟨⟨a', ha'⟩, hva⟩ := valAt_chart hU κ a
  rw [← hy] at hvb hva
  have hb1 : (Scheme.stalkClosedPointTo y).hom b' = κ b := by rw [← hvb, ← hb', Base.valAt_stalk]
  have ha1 : (Scheme.stalkClosedPointTo y).hom a' = κ a := by rw [← hva, ← ha', Base.valAt_stalk]
  have hu : IsUnit b' := (isUnit_map_iff (Scheme.stalkClosedPointTo y).hom b').1 (by rw [hb1]; exact hb.isUnit)
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hg' : g = algebraMap _ X.functionField (a' * c) := by
    rw [map_mul, ha', ← hg, ← hb', mul_assoc, ← map_mul, hc, map_one, mul_one]
  rw [hg', Base.valAt_stalk, ← hb1, ← ha1, ← map_mul, mul_assoc, mul_comm c, hc, mul_one]

theorem place_eq {F : Type} [Field F] [NumberField F] {v v' : HeightOneSpectrum (𝓞 F)} (e : Ext v')
    (h : ∀ a ∈ v.asIdeal, ∃ c : e.O, (c : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F a) ∧ ¬ IsUnit c) :
    v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := fun a ha => by
    obtain ⟨c, hc, hu⟩ := h a ha
    have h1 : e.w c < 1 := not_le.1 fun h' => hu (RegCrit.isUnit_of_one_le e c h')
    rw [hc, e.w_alg] at h1
    rw [← FinitePlace.norm_lt_one_iff_mem F v' a, FinitePlace.norm_embedding]
    exact h1
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle).symm

theorem exists_hom (F : Type) [Field F] [NumberField F] (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (hinj : Function.Injective (algebraMap A K)) [Algebra (𝓞 F) A] [Algebra.FiniteType (𝓞 F) A] [CharZero A]
    (𝔪 : Ideal A) (t : K)
    (hne : 𝔪.map (algebraMap A (Algebra.adjoin A {t})) ⊔
      Ideal.span {(⟨t, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {t})} ≠ ⊤) (c : A) (hc : c ≠ 0) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : A →+* e.O) (τ : e.O),
      (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) A a) : e.O) : AlgebraicClosure F) =
        algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (∀ m ∈ 𝔪, ¬ IsUnit (φ m)) ∧ φ c ≠ 0 ∧ ¬ IsUnit τ ∧
      ∀ a b : A, t * algebraMap A K a = algebraMap A K b → τ * φ a = φ b := by
  let B := Algebra.adjoin A {t}
  have hB : Function.Injective (algebraMap A B) := fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra (𝓞 F) B := ((algebraMap A B).comp (algebraMap (𝓞 F) A)).toAlgebra
  have : IsScalarTower (𝓞 F) A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Algebra.FiniteType A B := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)
  have : Algebra.FiniteType (𝓞 F) B := Algebra.FiniteType.trans (S := A) inferInstance h1
  have : CharZero B := charZero_of_injective_algebraMap hB
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F B 𝔫 h𝔫 (algebraMap A B c) fun h => hc (hB (by rw [h, map_zero]))
  have hn : ∀ s ∈ 𝔫, ¬ IsUnit (φ s) := fun s hs => by
    rw [← h₂] at hs
    exact hs
  refine ⟨v, e, φ.comp (algebraMap A B), φ ⟨t, Algebra.subset_adjoin rfl⟩, h₁,
    fun m hm => hn _ (hle (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hm))), h₃,
    hn _ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))), fun a b hab => ?_⟩
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  exact congrArg φ (Subtype.ext hab)

open GlobalTheory.TrueGeo.HorizPt in

theorem main : RegLocSt := by
  intro F _ _ Y V U₀ W hW v g hf x hx hxv
  by_contra hreg
  have hg0 : g ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : U ≤ U₀ := hUW
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  have := functionField_isFractionRing_of_isAffineOpen V.X U hU
  obtain ⟨w, hw⟩ := hW
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le ⟨_, gen_mem hw⟩ (gen_mem hxU)
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hh
    exact hh
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(V.X, U)) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj := IsFractionRing.injective Γ(V.X, U) V.X.functionField
  have hb1 : algebraMap Γ(V.X, U) V.X.functionField b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  have hgb : g * algebraMap Γ(V.X, U) V.X.functionField b = algebraMap Γ(V.X, U) V.X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb1]
  obtain ⟨v', e, φ, τ, h₁, h₂, h₃, h₄, h₅⟩ := exists_hom F Γ(V.X, U) V.X.functionField hinj 𝔪 g⁻¹
    (ideal_ne_top hU hxU (V.normal x).2 h𝔪.ne_top hle' hg0 hreg) (b * h) (mul_ne_zero hb0 hh0)
  obtain rfl : v' = v := place_eq e fun c hc => by
    refine ⟨_, h₁ c, h₂ _ (hle' ?_)⟩
    have hx' : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    have hc' : c ∈ ((hU.fromSpec ≫ V.p) (hU.primeIdealOf ⟨x, hxU⟩)).asIdeal := by
      change c ∈ (V.p (hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩))).asIdeal
      rw [hx', hxv]
      exact hc
    rw [fromSpec_str] at hc'
    exact hc'
  have hτ : τ * φ a = φ b := h₅ a b (by rw [← hgb, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul])
  rw [map_mul] at h₃
  let κ : Γ(V.X, U) →+* AlgebraicClosure F := e.O.subtype.comp φ
  have hκ : ∀ s, φ s ≠ 0 → κ s ≠ 0 := fun s hs h => hs (Subtype.ext h)
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hyt : spMap e.O.subtype ≫ yt = Spec.map (CommRingCat.ofHom κ) ≫ hU.fromSpec := by
    simp only [yt]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  have hval := hf e (V.pb.lift _ _ hw) yt (V.pb.lift_snd _ _ hw) hy.symm
    (fun x _ => hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)) (by
      rw [hy, hyt]
      refine hhW ?_
      change PrimeSpectrum.comap κ (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen h
      rw [hU.fromSpec_preimage_basicOpen]
      intro h'
      have h'' : κ h ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h'
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h''
      exact hκ h (right_ne_zero_of_mul h₃) h'')
  rw [hy, hyt] at hval
  have hκb := hκ b (left_ne_zero_of_mul h₃)
  have hdiv := valAt_div hU κ a b hκb hgb
  have hτ' : (τ : AlgebraicClosure F) * κ a = κ b := congrArg Subtype.val hτ
  rw [← hdiv, ← mul_assoc] at hτ'
  have hone := congrArg e.w (mul_right_cancel₀ hκb (hτ'.trans (one_mul _).symm))
  rw [map_mul, map_one] at hone
  exact h₄ (RegCrit.isUnit_of_one_le e τ (hone.ge.trans (mul_le_of_le_one_right (e.w.nonneg _) hval)))

end GlobalTheory.DetHT.RegLoc
