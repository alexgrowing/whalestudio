import Mathlib

open MvPolynomial IsLocalRing

noncomputable section

namespace GlobalTheory

section Ideal

variable {O : Type*} [CommRing O]

abbrev gaussIdeal (p : Ideal O) (σ : Type*) : Ideal (MvPolynomial σ O) :=
  p.map (C : O →+* MvPolynomial σ O)

variable (p : Ideal O) (σ : Type*)

variable {p σ} in

theorem mem_gaussIdeal_iff {f : MvPolynomial σ O} :
    f ∈ gaussIdeal p σ ↔ ∀ m, f.coeff m ∈ p :=
  MvPolynomial.mem_map_C_iff

variable {p σ} in

theorem C_mem_gaussIdeal_iff {a : O} : (C a : MvPolynomial σ O) ∈ gaussIdeal p σ ↔ a ∈ p := by
  classical
  refine ⟨fun h ↦ by simpa using mem_gaussIdeal_iff.1 h 0, fun h ↦ Ideal.mem_map_of_mem _ h⟩

theorem comap_C_gaussIdeal : (gaussIdeal p σ).comap (C : O →+* MvPolynomial σ O) = p :=
  Ideal.ext fun _ ↦ C_mem_gaussIdeal_iff

instance gaussIdeal_liesOver : (gaussIdeal p σ).LiesOver p :=
  ⟨(comap_C_gaussIdeal p σ).symm⟩

def quotientGaussIdealEquiv :
    (MvPolynomial σ O ⧸ gaussIdeal p σ) ≃ₐ[O] MvPolynomial σ (O ⧸ p) :=
  (MvPolynomial.quotientEquivQuotientMvPolynomial p).symm

@[simp] theorem quotientGaussIdealEquiv_mk (f : MvPolynomial σ O) :
    quotientGaussIdealEquiv p σ (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk p) f := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

instance gaussIdeal_isPrime [p.IsPrime] : (gaussIdeal p σ).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (quotientGaussIdealEquiv p σ).toMulEquiv.isDomain _

variable {σ} in

theorem X_notMem_gaussIdeal [hp : p.IsPrime] (i : σ) :
    (X i : MvPolynomial σ O) ∉ gaussIdeal p σ := by
  classical
  intro h
  have := mem_gaussIdeal_iff.1 h (Finsupp.single i 1)
  rw [coeff_X_same] at this
  exact hp.ne_top ((Ideal.eq_top_iff_one _).2 this)

variable {p} in

theorem comap_map_gaussIdeal {O₂ : Type*} [CommRing O₂] (φ : O →+* O₂) (q : Ideal O₂)
    (h : p = q.comap φ) :
    gaussIdeal p σ = (gaussIdeal q σ).comap (MvPolynomial.map φ) := by
  ext f
  simp [mem_gaussIdeal_iff, h, coeff_map]

end Ideal

abbrev GaussLocal (O : Type*) [CommRing O] (p : Ideal O) [p.IsPrime] (σ : Type*) : Type _ :=
  Localization.AtPrime (p.map (C : O →+* MvPolynomial σ O))

abbrev GaussLocal' (O : Type*) [CommRing O] [IsLocalRing O] (σ : Type*) : Type _ :=
  GaussLocal O (maximalIdeal O) σ

namespace GaussLocal

variable {O : Type*} [CommRing O] (p : Ideal O) [p.IsPrime] (σ : Type*)

instance algebraAtPrime : Algebra (Localization.AtPrime p) (GaussLocal O p σ) :=
  Localization.AtPrime.algebraOfLiesOver p (gaussIdeal p σ)

instance isLiesOverAlgebra : Localization.AtPrime.IsLiesOverAlgebra p (gaussIdeal p σ) :=
  ⟨rfl⟩

theorem algebraMap_C (a : O) :
    algebraMap (MvPolynomial σ O) (GaussLocal O p σ) (C a) = algebraMap O (GaussLocal O p σ) a :=
  rfl

variable {p σ}

theorem algebraMap_base_mem_maximalIdeal_iff (a : O) :
    algebraMap O (GaussLocal O p σ) a ∈ maximalIdeal (GaussLocal O p σ) ↔ a ∈ p :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (gaussIdeal p σ) (C a)).trans
    C_mem_gaussIdeal_iff

theorem isUnit_algebraMap_base_iff (a : O) :
    IsUnit (algebraMap O (GaussLocal O p σ) a) ↔ a ∉ p := by
  rw [← notMem_maximalIdeal, algebraMap_base_mem_maximalIdeal_iff]

variable (p) in

theorem isUnit_X (i : σ) : IsUnit (algebraMap (MvPolynomial σ O) (GaussLocal O p σ) (X i)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff _ (gaussIdeal p σ) _).2 (X_notMem_gaussIdeal p i)

variable (p σ)

theorem map_eq_maximalIdeal :
    p.map (algebraMap O (GaussLocal O p σ)) = maximalIdeal (GaussLocal O p σ) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
  rfl

variable {p} in

theorem maximalIdeal_eq_span {a : O} (h : p = Ideal.span {a}) :
    maximalIdeal (GaussLocal O p σ) = Ideal.span {algebraMap O (GaussLocal O p σ) a} := by
  rw [← map_eq_maximalIdeal, ← Set.image_singleton, ← Ideal.map_span, ← h]

instance maximalIdeal_liesOver : (maximalIdeal (GaussLocal O p σ)).LiesOver p :=
  ⟨Ideal.ext fun a ↦ (algebraMap_base_mem_maximalIdeal_iff a).symm⟩

instance flat : Module.Flat O (GaussLocal O p σ) := inferInstance

instance flat_atPrime : Module.Flat (Localization.AtPrime p) (GaussLocal O p σ) :=
  (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).2 inferInstance

instance faithfullyFlat_atPrime :
    Module.FaithfullyFlat (Localization.AtPrime p) (GaussLocal O p σ) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

section Domain

variable [IsDomain O]

instance isDomain : IsDomain (GaussLocal O p σ) := inferInstance

instance isFractionRing : IsFractionRing (GaussLocal O p σ) (FractionRing (MvPolynomial σ O)) :=
  inferInstance

instance isScalarTower_fractionRing :
    IsScalarTower O (GaussLocal O p σ) (FractionRing (MvPolynomial σ O)) :=
  .of_algebraMap_eq fun a ↦ by
    rw [← algebraMap_C, ← IsScalarTower.algebraMap_apply]; rfl

theorem algebraMap_injective :
    Function.Injective (algebraMap (MvPolynomial σ O) (GaussLocal O p σ)) :=
  FaithfulSMul.algebraMap_injective _ _

instance faithfulSMul : FaithfulSMul O (GaussLocal O p σ) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2
    ((algebraMap_injective p σ).comp (C_injective σ O))

end Domain

section Local

variable (O) [IsLocalRing O]

instance isLocalHom : IsLocalHom (algebraMap O (GaussLocal' O σ)) :=
  ⟨fun a h ↦ notMem_maximalIdeal.1 ((isUnit_algebraMap_base_iff a).1 h)⟩

instance faithfullyFlat : Module.FaithfullyFlat O (GaussLocal' O σ) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

end Local

section Residue

variable {p} {k : Type*} [Field k] (φ : O →+* k) (hφ : RingHom.ker φ = p)

def reduction : GaussLocal O p σ →+* FractionRing (MvPolynomial σ k) :=
  IsLocalization.lift (M := (gaussIdeal p σ).primeCompl)
    (g := (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))).comp
      (MvPolynomial.map φ)) fun y ↦ by
    refine IsUnit.mk0 _ fun h ↦ y.2 ?_
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hφ] at h
    exact h

@[simp] theorem reduction_algebraMap (f : MvPolynomial σ O) :
    reduction σ φ hφ (algebraMap _ _ f) = algebraMap _ _ (MvPolynomial.map φ f) :=
  IsLocalization.lift_eq _ _

theorem ker_reduction : RingHom.ker (reduction σ φ hφ) = maximalIdeal (GaussLocal O p σ) := by
  refine ((maximalIdeal.isMaximal _).eq_of_le (RingHom.ker_ne_top _) ?_).symm
  rw [← map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [← hφ, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_C, reduction_algebraMap, map_C, ha]
  simp

instance isLocalHom_reduction : IsLocalHom (reduction σ φ hφ) :=
  ⟨fun a h ↦ by
    rw [← notMem_maximalIdeal, ← ker_reduction σ φ hφ]
    exact h.ne_zero⟩

theorem lift_reduction_bijective (hk : ∀ c : k, ∃ a b : O, c = φ a / φ b) :
    Function.Bijective (ResidueField.lift (reduction σ φ hφ)) := by
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  set F := ResidueField.lift (reduction σ φ hφ) with hF
  have h0 : ∀ f : MvPolynomial σ O, algebraMap _ _ (MvPolynomial.map φ f) ∈ F.fieldRange :=
    fun f ↦ ⟨residue _ (algebraMap _ _ f), by
      rw [hF, ResidueField.lift_residue_apply, reduction_algebraMap]⟩
  have h1 : ∀ g : MvPolynomial σ k, algebraMap _ _ g ∈ F.fieldRange := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨a, b, rfl⟩ := hk c
      have := div_mem (h0 (C a)) (h0 (C b))
      rw [map_C, map_C] at this
      have e := map_div₀ ((algebraMap (MvPolynomial σ k)
        (FractionRing (MvPolynomial σ k))).comp C) (φ a) (φ b)
      rw [RingHom.comp_apply] at e
      rw [e]
      exact this
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf =>
      rw [map_mul]
      refine mul_mem hf ?_
      simpa using h0 (X i)
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ k) x
  exact div_mem (h1 f) (h1 g)

variable (p)

theorem residueField_eq_div (c : p.ResidueField) :
    ∃ a b : O, c = algebraMap O p.ResidueField a / algebraMap O p.ResidueField b := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) c
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a, b, rfl⟩

def residueFieldEquiv :
    ResidueField (GaussLocal O p σ) ≃ₐ[p.ResidueField]
      FractionRing (MvPolynomial σ p.ResidueField) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _
    (lift_reduction_bijective σ (algebraMap O p.ResidueField) p.ker_algebraMap_residueField
      (residueField_eq_div p))) fun c ↦ by
    have : (ResidueField.lift (reduction σ (algebraMap O p.ResidueField)
        p.ker_algebraMap_residueField)).comp (algebraMap p.ResidueField _) = algebraMap _ _ := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      change ResidueField.lift _ (residue _ (algebraMap (MvPolynomial σ O) _ (C a))) = _
      rw [ResidueField.lift_residue_apply, reduction_algebraMap, map_C]
      rfl
    exact congr($this c)

@[simp] theorem residueFieldEquiv_residue (f : MvPolynomial σ O) :
    residueFieldEquiv p σ (residue _ (algebraMap _ _ f)) =
      algebraMap _ _ (MvPolynomial.map (algebraMap O p.ResidueField) f) :=
  reduction_algebraMap σ _ p.ker_algebraMap_residueField f

variable (O) in

def residueFieldEquiv' [IsLocalRing O] :
    ResidueField (GaussLocal' O σ) ≃ₐ[ResidueField O]
      FractionRing (MvPolynomial σ (ResidueField O)) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _
    (lift_reduction_bijective σ (residue O) ker_residue fun c ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective c
      exact ⟨a, 1, by simp⟩)) fun c ↦ by
    obtain ⟨a, rfl⟩ := residue_surjective c
    refine (reduction_algebraMap σ (residue O) ker_residue (C a)).trans ?_
    rw [map_C]
    rfl

@[simp] theorem residueFieldEquiv'_residue [IsLocalRing O] (f : MvPolynomial σ O) :
    residueFieldEquiv' O σ (residue _ (algebraMap _ _ f)) =
      algebraMap _ _ (MvPolynomial.map (residue O) f) :=
  reduction_algebraMap σ _ ker_residue f

end Residue

section Map

variable {p} {O₂ : Type*} [CommRing O₂] {q : Ideal O₂} [q.IsPrime]

def map (φ : O →+* O₂) (h : p = q.comap φ) : GaussLocal O p σ →+* GaussLocal O₂ q σ :=
  Localization.localRingHom _ _ (MvPolynomial.map φ) (comap_map_gaussIdeal σ φ q h)

@[simp] theorem map_algebraMap (φ : O →+* O₂) (h : p = q.comap φ) (f : MvPolynomial σ O) :
    map σ φ h (algebraMap _ _ f) = algebraMap _ _ (MvPolynomial.map φ f) :=
  Localization.localRingHom_to_map _ _ _ _ _

instance isLocalHom_map (φ : O →+* O₂) (h : p = q.comap φ) : IsLocalHom (map σ φ h) :=
  Localization.isLocalHom_localRingHom _ _ _ _

@[simp] theorem map_algebraMap_base (φ : O →+* O₂) (h : p = q.comap φ) (a : O) :
    map σ φ h (algebraMap O _ a) = algebraMap O₂ _ (φ a) := by
  rw [← algebraMap_C, map_algebraMap, map_C, algebraMap_C]

@[simp] theorem map_id : map σ (RingHom.id O) (Ideal.comap_id p).symm = RingHom.id _ :=
  Localization.localRingHom_unique _ _ _ _ fun f ↦ by simp [MvPolynomial.map_id]

variable (p) (A : Type*) [CommRing A] [Algebra O A] [IsLocalRing A] [IsLocalization.AtPrime A p]

theorem map_bijective_of_isLocalization :
    Function.Bijective (map σ (algebraMap O A) (IsLocalization.AtPrime.under_maximalIdeal A p).symm :
      GaussLocal O p σ →+* GaussLocal' A σ) := by
  let : Algebra (MvPolynomial σ O) (MvPolynomial σ A) := MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := σ) p.primeCompl A
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (p.primeCompl.map (C : O →+* MvPolynomial σ O)) (GaussLocal' A σ)
    (gaussIdeal (maximalIdeal A) σ)
  have e : gaussIdeal p σ = (gaussIdeal (maximalIdeal A) σ).comap
      (algebraMap (MvPolynomial σ O) (MvPolynomial σ A)) :=
    comap_map_gaussIdeal σ (algebraMap O A) _ (IsLocalization.AtPrime.under_maximalIdeal A p).symm
  have : IsLocalization.AtPrime (GaussLocal' A σ) (gaussIdeal p σ) := by
    convert h
  refine IsLocalization.bijective (gaussIdeal p σ).primeCompl _ ?_
  exact RingHom.ext fun f ↦ map_algebraMap σ (algebraMap O A)
    (IsLocalization.AtPrime.under_maximalIdeal A p).symm f

def mapLocalization : GaussLocal O p σ →ₐ[O] GaussLocal' A σ where
  toRingHom := map σ (algebraMap O A) (IsLocalization.AtPrime.under_maximalIdeal A p).symm
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply O A (GaussLocal' A σ) a]
    exact map_algebraMap_base σ (algebraMap O A)
      (IsLocalization.AtPrime.under_maximalIdeal A p).symm a

theorem mapLocalization_toRingHom :
    (mapLocalization p σ A : GaussLocal O p σ →+* GaussLocal' A σ) =
      map σ (algebraMap O A) (IsLocalization.AtPrime.under_maximalIdeal A p).symm := rfl

def equivOfIsLocalization : GaussLocal O p σ ≃ₐ[O] GaussLocal' A σ :=
  AlgEquiv.ofBijective (mapLocalization p σ A) <| by
    rw [← AlgHom.coe_toRingHom, mapLocalization_toRingHom]
    exact map_bijective_of_isLocalization p σ A

@[simp] theorem equivOfIsLocalization_algebraMap (f : MvPolynomial σ O) :
    equivOfIsLocalization p σ A (algebraMap _ _ f) =
      algebraMap _ _ (MvPolynomial.map (algebraMap O A) f) := by
  rw [equivOfIsLocalization, AlgEquiv.ofBijective_apply, ← AlgHom.coe_toRingHom,
    mapLocalization_toRingHom, map_algebraMap]

end Map

section Examples

local instance isPrime_span_two : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two

example : IsUnit (algebraMap (MvPolynomial Unit ℤ) (GaussLocal ℤ (Ideal.span {2}) Unit)
    (X () + C 2)) := by
  rw [map_add]
  have h2 : algebraMap (MvPolynomial Unit ℤ) (GaussLocal ℤ (Ideal.span {2}) Unit) (C 2) ∈
      maximalIdeal _ :=
    (algebraMap_base_mem_maximalIdeal_iff 2).2 (Ideal.mem_span_singleton_self 2)
  rw [← notMem_maximalIdeal, Ideal.add_mem_iff_left _ h2, notMem_maximalIdeal]
  exact isUnit_X _ ()

example : ¬ IsField (GaussLocal ℤ (Ideal.span {2}) Unit) := by
  rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span Unit rfl, Ideal.span_singleton_eq_bot,
    FaithfulSMul.algebraMap_eq_zero_iff]
  exact two_ne_zero

example [IsNoetherianRing O] [Finite σ] : IsNoetherianRing (GaussLocal O p σ) := inferInstance

example : IsScalarTower O (MvPolynomial σ O) (GaussLocal O p σ) ∧
    IsScalarTower O (Localization.AtPrime p) (GaussLocal O p σ) ∧
    IsLocalHom (algebraMap (Localization.AtPrime p) (GaussLocal O p σ)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Examples

end GaussLocal

end GlobalTheory
