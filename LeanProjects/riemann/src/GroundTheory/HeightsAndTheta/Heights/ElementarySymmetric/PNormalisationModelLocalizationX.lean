import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalisationModelLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

namespace NormalisationModelLocalization

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}

theorem disjoint_primeCompl (hq : q ∈ zeroSet J) :
    Disjoint ((RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl : Set (MvPolynomial (Fin n) ℂ))
      (J : Set (MvPolynomial (Fin n) ℂ)) := by
  rw [Set.disjoint_left]
  intro f hf hfJ
  exact hf (RingHom.mem_ker.2 (hq f hfJ))

theorem isPrime_map (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J hJ (disjoint_primeCompl hq)

theorem isDomain (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : IsDomain (curveLocalRing J q) := by
  haveI := isPrime_map hJ hq
  exact Ideal.Quotient.isDomain _

theorem algebraMap_eq_zero_iff (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f = 0 ↔ f ∈ J := by
  change Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]
  have h := IsLocalization.under_map_of_isPrime_disjoint (M := (RingHom.ker (eval q)).primeCompl)
    (S := Localization.AtPrime (RingHom.ker (eval q))) hJ (disjoint_primeCompl hq)
  rw [Ideal.under] at h
  rw [h]

def toFrac (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →+* FractionRing (curveLocalRing J q) :=
  (algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q))).comp
    (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q))

theorem toFrac_eq_zero_iff (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (f : MvPolynomial (Fin n) ℂ) :
    toFrac J q f = 0 ↔ f ∈ J := by
  rw [toFrac, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), algebraMap_eq_zero_iff hJ hq]

theorem toFrac_mem (f : MvPolynomial (Fin n) ℂ) :
    toFrac J q f ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) :=
  Subalgebra.algebraMap_mem _ _

variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem rename_mem_iff (f : MvPolynomial (Fin n) ℂ) : rename Sum.inl f ∈ M.ideal ↔ f ∈ J := by
  constructor
  · intro h
    rw [← M.comap_eq]
    exact h
  · intro h
    rw [← M.comap_eq] at h
    exact h

def num (i : Fin M.m) : MvPolynomial (Fin n) ℂ := (M.birational i).choose

def den (i : Fin M.m) : MvPolynomial (Fin n) ℂ := (M.birational i).choose_spec.choose

theorem den_not_mem (i : Fin M.m) : den M i ∉ J := (M.birational i).choose_spec.choose_spec.1

theorem den_mul_sub_mem (i : Fin M.m) :
    rename Sum.inl (den M i) * X (Sum.inr i) - rename Sum.inl (num M i) ∈ M.ideal :=
  (M.birational i).choose_spec.choose_spec.2

def denProd : MvPolynomial (Fin n) ℂ := ∏ i, den M i

def relIdeal : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :=
  Ideal.span (Set.range fun i => rename Sum.inl (den M i) * X (Sum.inr i) - rename Sum.inl (num M i))

theorem relIdeal_le : relIdeal M ≤ M.ideal := by
  rw [relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact den_mul_sub_mem M i

theorem clear (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (g : MvPolynomial (Fin n) ℂ),
      rename Sum.inl (denProd M) ^ N * h - rename Sum.inl g ∈ relIdeal M := by
  induction h using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, by simp⟩
  | add p r hp hr =>
    obtain ⟨N₁, g₁, h₁⟩ := hp
    obtain ⟨N₂, g₂, h₂⟩ := hr
    refine ⟨N₁ + N₂, denProd M ^ N₂ * g₁ + denProd M ^ N₁ * g₂, ?_⟩
    have e : rename Sum.inl (denProd M) ^ (N₁ + N₂) * (p + r) -
        rename Sum.inl (denProd M ^ N₂ * g₁ + denProd M ^ N₁ * g₂) =
        rename Sum.inl (denProd M) ^ N₂ * (rename Sum.inl (denProd M) ^ N₁ * p - rename Sum.inl g₁) +
          rename Sum.inl (denProd M) ^ N₁ * (rename Sum.inl (denProd M) ^ N₂ * r - rename Sum.inl g₂) := by
      simp only [map_add, map_mul, map_pow]
      ring
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p s hp =>
    obtain ⟨N, g, hg⟩ := hp
    cases s with
    | inl i =>
      refine ⟨N, g * X i, ?_⟩
      have e : rename Sum.inl (denProd M) ^ N * (p * X (Sum.inl i)) - rename Sum.inl (g * X i) =
          (rename Sum.inl (denProd M) ^ N * p - rename Sum.inl g) * X (Sum.inl i) := by
        simp only [map_mul, rename_X]
        ring
      rw [e]
      exact Ideal.mul_mem_right _ _ hg
    | inr i =>
      set c := ∏ j ∈ Finset.univ.erase i, den M j with hc
      have hB : denProd M = den M i * c := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      refine ⟨N + 1, g * c * num M i, ?_⟩
      have e : rename Sum.inl (denProd M) ^ (N + 1) * (p * X (Sum.inr i)) - rename Sum.inl (g * c * num M i) =
          (rename Sum.inl (denProd M) ^ N * p - rename Sum.inl g) * (rename Sum.inl (denProd M) * X (Sum.inr i)) +
            rename Sum.inl g * rename Sum.inl c *
              (rename Sum.inl (den M i) * X (Sum.inr i) - rename Sum.inl (num M i)) := by
        rw [hB]
        simp only [map_mul]
        ring
      rw [e]
      exact add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

def toFracModel (q : Fin n → ℂ) : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* FractionRing (curveLocalRing J q) :=
  eval₂Hom ((toFrac J q).comp C)
    (Sum.elim (fun j => toFrac J q (X j)) (fun i => toFrac J q (num M i) * Ring.inverse (toFrac J q (den M i))))

theorem toFracModel_rename (f : MvPolynomial (Fin n) ℂ) : toFracModel M q (rename Sum.inl f) = toFrac J q f := by
  rw [toFracModel, eval₂Hom_rename]
  have e : eval₂Hom ((toFrac J q).comp C) (Sum.elim (fun j => toFrac J q (X j))
      (fun i => toFrac J q (num M i) * Ring.inverse (toFrac J q (den M i))) ∘ Sum.inl) = toFrac J q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      simp
  rw [e]

variable {M}

theorem relIdeal_le_ker (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : relIdeal M ≤ RingHom.ker (toFracModel M q) := by
  have := isDomain hJ hq
  rw [relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hu : IsUnit (toFrac J q (den M i)) :=
    isUnit_iff_ne_zero.2 (fun h => den_not_mem M i ((toFrac_eq_zero_iff hJ hq _).1 h))
  simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, toFracModel_rename]
  rw [toFracModel, eval₂Hom_X', Sum.elim_inr, mul_left_comm, Ring.mul_inverse_cancel _ hu, mul_one, sub_self]

theorem ker_toFracModel (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : RingHom.ker (toFracModel M q) = M.ideal := by
  have := isDomain hJ hq
  have hBJ : toFrac J q (denProd M) ≠ 0 := by
    rw [denProd, map_prod]
    exact Finset.prod_ne_zero_iff.2 (fun i _ h => den_not_mem M i ((toFrac_eq_zero_iff hJ hq _).1 h))
  have hBM : rename Sum.inl (denProd M) ∉ M.ideal :=
    fun h => hBJ ((toFrac_eq_zero_iff hJ hq _).2 ((rename_mem_iff M _).1 h))
  ext h
  obtain ⟨N, g, hg⟩ := clear M h
  have hφ := relIdeal_le_ker hJ hq hg
  rw [RingHom.mem_ker, map_sub, map_mul, map_pow, toFracModel_rename, toFracModel_rename, sub_eq_zero] at hφ
  have hM := relIdeal_le M hg
  rw [RingHom.mem_ker]
  constructor
  · intro h0
    rw [h0, mul_zero, eq_comm, toFrac_eq_zero_iff hJ hq] at hφ
    have hg' : rename Sum.inl g ∈ M.ideal := (rename_mem_iff M g).2 hφ
    have hmul : rename Sum.inl (denProd M) ^ N * h ∈ M.ideal := by
      have := M.ideal.add_mem hM hg'
      rwa [sub_add_cancel] at this
    exact (M.isPrime.mem_or_mem hmul).resolve_left (fun hp => hBM (M.isPrime.mem_of_pow_mem N hp))
  · intro hh
    have hg' : rename Sum.inl g ∈ M.ideal := by
      have := M.ideal.sub_mem (M.ideal.mul_mem_left (rename Sum.inl (denProd M) ^ N) hh) hM
      rwa [sub_sub_cancel] at this
    rw [(toFrac_eq_zero_iff hJ hq g).2 ((rename_mem_iff M g).1 hg')] at hφ
    exact (mul_eq_zero.1 hφ).resolve_left (pow_ne_zero _ hBJ)

variable (M)

def modelToFrac (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) →+* FractionRing (curveLocalRing J q) :=
  Ideal.Quotient.lift M.ideal (toFracModel M q) (fun a ha => by
    rw [← RingHom.mem_ker, ker_toFracModel hJ hq]
    exact ha)

theorem modelToFrac_mk (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    modelToFrac M hJ hq (Ideal.Quotient.mk M.ideal h) = toFracModel M q h :=
  Ideal.Quotient.lift_mk _ _ _

theorem modelToFrac_injective (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : Function.Injective (modelToFrac M hJ hq) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [modelToFrac_mk, ← RingHom.mem_ker, ker_toFracModel hJ hq] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.2 hx

theorem modelToFrac_isUnit (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (y : normalModelSubmonoid M q) :
    IsUnit (modelToFrac M hJ hq y) := by
  obtain ⟨f, hf, hfy⟩ := y.2
  have hy : (y : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = Ideal.Quotient.mk M.ideal (rename Sum.inl f) :=
    hfy.symm
  rw [hy, modelToFrac_mk, toFracModel_rename]
  exact (isUnit_algebraMap_curveLocalRing J q f (fun h0 => hf (RingHom.mem_ker.2 h0))).map
    (algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)))

def locToFrac (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    Localization (normalModelSubmonoid M q) →+* FractionRing (curveLocalRing J q) :=
  IsLocalization.lift (M := normalModelSubmonoid M q) (S := Localization (normalModelSubmonoid M q))
    (modelToFrac_isUnit M hJ hq)

theorem locToFrac_algebraMap (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (r : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :
    locToFrac M hJ hq (algebraMap _ _ r) = modelToFrac M hJ hq r := by
  rw [locToFrac]
  exact IsLocalization.lift_eq _ _

theorem locToFrac_injective (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : Function.Injective (locToFrac M hJ hq) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (normalModelSubmonoid M q) z
  rw [locToFrac, IsLocalization.lift_mk'_spec, mul_zero] at hz
  rw [modelToFrac_injective M hJ hq (hz.trans (map_zero _).symm)]
  exact IsLocalization.mk'_zero _

def polyLocToModel : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+*
    Localization (normalModelSubmonoid M q) :=
  IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl)
    (S := Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
    (P := Localization (normalModelSubmonoid M q))
    (g := (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))).comp
      ((Ideal.Quotient.mk M.ideal).comp
        (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom))
    (fun y => IsLocalization.map_units (Localization (normalModelSubmonoid M q))
      (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : normalModelSubmonoid M q))

theorem polyLocToModel_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    polyLocToModel M (algebraMap _ _ f) =
      algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
        (Ideal.Quotient.mk M.ideal (rename Sum.inl f)) := by
  rw [polyLocToModel]
  exact IsLocalization.lift_eq _ _

def locToModel : curveLocalRing J q →+* Localization (normalModelSubmonoid M q) :=
  Ideal.Quotient.lift _ (polyLocToModel M) (fun a ha => by
    have hle : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
        RingHom.ker (polyLocToModel M) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker, polyLocToModel_algebraMap,
        Ideal.Quotient.eq_zero_iff_mem.2 ((rename_mem_iff M f).2 hf), map_zero]
    exact hle ha)

theorem locToFrac_comp (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (locToFrac M hJ hq).comp (locToModel M) = algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl
  refine RingHom.ext fun f => ?_
  change locToFrac M hJ hq (polyLocToModel M (algebraMap _ _ f)) = toFrac J q f
  rw [polyLocToModel_algebraMap, locToFrac_algebraMap, modelToFrac_mk, toFracModel_rename]

theorem toFracModel_mem (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    toFracModel M q h ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
  have hX : ∀ s, toFracModel M q (X s) ∈
      integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
    intro s
    cases s with
    | inl j =>
      rw [← rename_X (R := ℂ) (Sum.inl : Fin n → Fin n ⊕ Fin M.m) j, toFracModel_rename]
      exact toFrac_mem _
    | inr i =>
      obtain ⟨P, hPm, hP⟩ := M.integral i
      have h0 : toFracModel M q (P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] _).toRingHom
          (X (Sum.inr i))) = 0 := by
        rw [← RingHom.mem_ker, ker_toFracModel hJ hq]
        exact hP
      rw [Polynomial.hom_eval₂] at h0
      have hc : (toFracModel M q).comp (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] _).toRingHom =
          (algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q))).comp
            (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q)) :=
        RingHom.ext (toFracModel_rename M)
      rw [hc] at h0
      refine ⟨P.map (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q)), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact h0
  induction h using MvPolynomial.induction_on with
  | C c =>
    rw [← rename_C (R := ℂ) (Sum.inl : Fin n → Fin n ⊕ Fin M.m) c, toFracModel_rename]
    exact toFrac_mem _
  | add p r hp hr =>
    rw [map_add]
    exact add_mem hp hr
  | mul_X p s hp =>
    rw [map_mul]
    exact mul_mem hp (hX s)

theorem locToFrac_mem (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (z : Localization (normalModelSubmonoid M q)) :
    locToFrac M hJ hq z ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (normalModelSubmonoid M q) z
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨f, hf, hfs⟩ := s.2
  have hs : (s : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = Ideal.Quotient.mk M.ideal (rename Sum.inl f) :=
    hfs.symm
  obtain ⟨u, hu⟩ := isUnit_algebraMap_curveLocalRing J q f (fun h0 => hf (RingHom.mem_ker.2 h0))
  have key : locToFrac M hJ hq (IsLocalization.mk' _ (Ideal.Quotient.mk M.ideal h) s) =
      toFracModel M q h * algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)) ↑u⁻¹ := by
    rw [locToFrac, IsLocalization.lift_mk'_spec, hs, modelToFrac_mk, modelToFrac_mk, toFracModel_rename, toFrac,
      RingHom.comp_apply, ← hu, mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
  rw [key]
  exact mul_mem (toFracModel_mem M hJ hq h) (Subalgebra.algebraMap_mem _ _)

theorem exists_locToFrac (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (x : FractionRing (curveLocalRing J q))
    (hx : IsIntegral (curveLocalRing J q) x) : ∃ z, locToFrac M hJ hq z = x := by
  have := isDomain hJ hq
  have := M.isPrime
  haveI : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) := M.isIntegrallyClosed
  letI : Algebra (Localization (normalModelSubmonoid M q)) (FractionRing (curveLocalRing J q)) :=
    (locToFrac M hJ hq).toAlgebra
  have hinj := locToFrac_injective M hJ hq
  haveI : IsDomain (Localization (normalModelSubmonoid M q)) :=
    Function.Injective.isDomain (locToFrac M hJ hq) hinj
  haveI : IsIntegrallyClosed (Localization (normalModelSubmonoid M q)) :=
    isIntegrallyClosed_of_isLocalization _ (normalModelSubmonoid M q)
      (fun s hs => mem_nonZeroDivisors_of_ne_zero (fun h0 => zero_not_mem_normalModelSubmonoid M q hq (h0 ▸ hs)))
  haveI : IsFractionRing (Localization (normalModelSubmonoid M q)) (FractionRing (curveLocalRing J q)) := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · intro y
      refine isUnit_iff_ne_zero.2 (fun h0 => nonZeroDivisors.coe_ne_zero y ?_)
      exact (injective_iff_map_eq_zero _).1 hinj _ h0
    · intro z
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (curveLocalRing J q)) z
      have hb : locToModel M (b : curveLocalRing J q) ≠ 0 := by
        intro h0
        have h1 := congrArg (locToFrac M hJ hq) h0
        rw [← RingHom.comp_apply, locToFrac_comp, map_zero] at h1
        exact nonZeroDivisors.coe_ne_zero b ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective _ _) _ h1)
      refine ⟨⟨locToModel M a, ⟨locToModel M b, mem_nonZeroDivisors_of_ne_zero hb⟩⟩, ?_⟩
      change z * locToFrac M hJ hq (locToModel M b) = locToFrac M hJ hq (locToModel M a)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, locToFrac_comp]
      exact hab
    · intro a b hab
      exact ⟨1, by rw [hinj hab]⟩
  have hx' : IsIntegral (Localization (normalModelSubmonoid M q)) x := by
    obtain ⟨p, hpm, hp⟩ := hx
    refine ⟨p.map (locToModel M), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, locToFrac_comp]
    exact hp
  exact (IsIntegrallyClosed.isIntegral_iff (K := FractionRing (curveLocalRing J q))).1 hx'

end NormalisationModelLocalization

open NormalisationModelLocalization in

theorem NormalisationModelLocalization.proof : NormalisationModelLocalization.Statement := by
  intro n J q M hJ
  by_cases hq : q ∈ zeroSet J
  · let g : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q :=
      (locToFrac M hJ hq).codRestrict (integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)))
        (locToFrac_mem M hJ hq)
    have hbij : Function.Bijective g := by
      refine ⟨fun a b h => locToFrac_injective M hJ hq (congrArg Subtype.val h), ?_⟩
      rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := exists_locToFrac M hJ hq x hx
      exact ⟨z, Subtype.ext hz⟩
    refine ⟨(RingEquiv.ofBijective g hbij).symm, fun f => ?_⟩
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    change toFrac J q f = locToFrac M hJ hq (algebraMap _ _ (Ideal.Quotient.mk M.ideal (rename Sum.inl f)))
    rw [locToFrac_algebraMap, modelToFrac_mk, toFracModel_rename]
  · haveI := curveLocalRing_subsingleton J q hq
    haveI : Subsingleton (FractionRing (curveLocalRing J q)) :=
      IsLocalization.subsingleton (M := nonZeroDivisors (curveLocalRing J q))
        (by rw [Subsingleton.elim (0 : curveLocalRing J q) 1]; exact one_mem _)
    haveI : Subsingleton (curveNormalisation J q) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := FractionRing (curveLocalRing J q)) _ _)⟩
    have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∈ normalModelSubmonoid M q := by
      simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hq
      obtain ⟨g, hg, hgq⟩ := hq
      have h1 := mk_rename_mem_normalModelSubmonoid M q g hgq
      rwa [Ideal.Quotient.eq_zero_iff_mem.2 ((rename_mem_iff M g).2 hg)] at h1
    haveI : Subsingleton (Localization (normalModelSubmonoid M q)) := IsLocalization.subsingleton h0
    let e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q) :=
      { toFun := fun _ => 0
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    exact ⟨e, fun _ => Subsingleton.elim _ _⟩

end

end GroundTheory.Heights₂.Heights
