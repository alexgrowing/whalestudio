import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox

theorem essFiniteType_loc {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.EssFiniteType ℤ (loc S) := by
  haveI : Module.Finite (gen S) (integralClosure (gen S) (FractionRing (gen S))) :=
    GlobalTheory.finite_integralClosure_of_essFiniteType_int (gen S)
  haveI : Algebra.EssFiniteType ℤ (gen S) := Algebra.EssFiniteType.of_finiteType ℤ _
  haveI : Algebra.EssFiniteType (gen S) (integralClosure (gen S) (FractionRing (gen S))) := inferInstance
  haveI h1 : Algebra.EssFiniteType ℤ (integralClosure (gen S) (FractionRing (gen S))) :=
    Algebra.EssFiniteType.comp ℤ (gen S) _
  have h2 : (algebraMap ℤ (norm S)).EssFiniteType := by
    have e : algebraMap ℤ (norm S) =
        (normEquiv S).symm.toRingHom.comp (algebraMap ℤ (integralClosure (gen S) (FractionRing (gen S)))) :=
      RingHom.ext_int _ _
    rw [e]
    exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 h1)
      (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_surjective (normEquiv S).symm.toRingHom (normEquiv S).symm.surjective))
  haveI : Algebra.EssFiniteType ℤ (norm S) := RingHom.essFiniteType_algebraMap.1 h2
  haveI := loc_isLocalization S
  haveI : Algebra.EssFiniteType (norm S) (loc S) := Algebra.EssFiniteType.of_isLocalization _ (unitsIn S)
  exact Algebra.EssFiniteType.comp ℤ (norm S) (loc S)

end GlobalTheory.VertUnitsNoeth

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox TensorProduct

theorem exists_model {T : Type} [CommRing T] [IsDomain T]
    (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
    (ys : Finset E) (s : T) :
    ∃ S : Finset T, s ∈ loc S ∧ ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (loc S)) EA)
      (_ : Algebra.Etale (Polynomial (loc S)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (loc S)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (loc S).subtype) ∧
      Function.Injective e ∧ ∀ y ∈ ys, y ∈ e.range := by
  classical
  obtain ⟨κ, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := Polynomial T) (S := E)).mp
      inferInstance |>.out
  have hsurj : ∀ y : E, ∃ f : MvPolynomial κ (Polynomial T), MvPolynomial.aeval P.val f = y := by
    intro y
    obtain ⟨f, hf⟩ := P.algebraMap_surjective y
    exact ⟨f, by rw [← hf, Algebra.Generators.algebraMap_apply]⟩
  choose f hf using hsurj
  have hfin : (P.coeffs ∪ ⋃ y ∈ ys, ((f y).coeffs : Set (Polynomial T))).Finite :=
    P.finite_coeffs.union (Set.Finite.biUnion ys.finite_toSet fun y _ => (f y).coeffs.finite_toSet)
  set S : Finset T := insert s (hfin.toFinset.biUnion Polynomial.coeffs) with hS
  have hcoef : ∀ p ∈ P.coeffs ∪ ⋃ y ∈ ys, ((f y).coeffs : Set (Polynomial T)),
      p ∈ (Polynomial.mapRingHom (loc S).subtype).range := by
    intro p hp
    rw [Polynomial.mem_map_range]
    intro n
    by_cases h : p.coeff n = 0
    · rw [h]; exact zero_mem _
    · exact ⟨⟨_, mem_loc_of_mem S (Finset.mem_insert_of_mem (Finset.mem_biUnion.2
        ⟨p, hfin.mem_toFinset.2 hp, Polynomial.coeff_mem_coeffs h⟩))⟩, rfl⟩
  refine ⟨S, mem_loc_of_mem S (Finset.mem_insert_self _ _), ?_⟩
  letI : Algebra (Polynomial (loc S)) (Polynomial T) := (Polynomial.mapRingHom (loc S).subtype).toAlgebra
  letI : Algebra (Polynomial (loc S)) E :=
    ((algebraMap (Polynomial T) E).comp (algebraMap (Polynomial (loc S)) (Polynomial T))).toAlgebra
  haveI : IsScalarTower (Polynomial (loc S)) (Polynomial T) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : P.HasCoeffs (Polynomial (loc S)) := ⟨fun p hp => hcoef p (Or.inl hp)⟩
  haveI : FaithfulSMul (Polynomial (loc S)) (Polynomial T) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (Polynomial.map_injective _ Subtype.val_injective)
  let Q := P.ofHasCoeffs (Polynomial (loc S))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial (loc S))
      (P.ModelOfHasCoeffs (Polynomial (loc S))) :=
    Q.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  haveI : Algebra.Etale (Polynomial (loc S)) (P.ModelOfHasCoeffs (Polynomial (loc S))) := inferInstance
  let e : P.ModelOfHasCoeffs (Polynomial (loc S)) →+* E :=
    (P.tensorModelOfHasCoeffsEquiv (Polynomial (loc S))).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Polynomial (loc S)) (A := Polynomial T)).toRingHom
  have he : ∀ y, e y = P.tensorModelOfHasCoeffsEquiv (Polynomial (loc S)) (1 ⊗ₜ y) := fun _ => rfl
  refine ⟨P.ModelOfHasCoeffs (Polynomial (loc S)), inferInstance, inferInstance, inferInstance, e, ?_, ?_, ?_⟩
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, he, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : (algebraMap (Polynomial (loc S)) (Polynomial T) x) ⊗ₜ[Polynomial (loc S)]
        (1 : P.ModelOfHasCoeffs (Polynomial (loc S))) =
        algebraMap (Polynomial T) (Polynomial T ⊗[Polynomial (loc S)] P.ModelOfHasCoeffs (Polynomial (loc S)))
          (algebraMap (Polynomial (loc S)) (Polynomial T) x) := rfl
    rw [this, AlgEquiv.commutes]
    rfl
  · intro a b hab
    have hinj : Function.Injective (Algebra.linearMap (Polynomial (loc S)) (Polynomial T)) :=
      Polynomial.map_injective _ Subtype.val_injective
    have h2 := Module.Flat.rTensor_preserves_injective_linearMap
      (M := P.ModelOfHasCoeffs (Polynomial (loc S))) _ hinj
    have h3 : (1 : Polynomial (loc S)) ⊗ₜ[Polynomial (loc S)] a = 1 ⊗ₜ b := by
      apply h2
      simp only [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
      exact (P.tensorModelOfHasCoeffsEquiv (Polynomial (loc S))).injective hab
    have h4 := congrArg (TensorProduct.lid (Polynomial (loc S)) _) h3
    simpa using h4
  · intro y hy
    have hy' : f y ∈ Set.range (MvPolynomial.map (algebraMap (Polynomial (loc S)) (Polynomial T))) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨a, ha⟩ := hcoef c (Or.inr (Set.mem_biUnion hy hc))
      exact ⟨a, ha⟩
    obtain ⟨g, hg⟩ := hy'
    refine ⟨Ideal.Quotient.mk _ g, ?_⟩
    rw [he, Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
      ← MvPolynomial.aeval_map_algebraMap (Polynomial T), hg, hf]

end GlobalTheory.VertUnitsNoeth

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox

theorem mem_originIdeal_iff' {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤ (maximalIdeal T).comap (Polynomial.constantCoeff (R := T)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    have := hle hf
    simpa [Polynomial.coeff_zero_eq_eval_zero] using this
  · intro hf
    have h1 : Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_sub_C))
    simpa using Ideal.add_mem _ h1 h2

theorem comap_originIdeal' (A T : Type) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    (i : A →+* T) [IsLocalHom i] :
    (GlobalTheory.KeyOriginCut.originIdeal T).comap (Polynomial.mapRingHom i) = GlobalTheory.KeyOriginCut.originIdeal A := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff', mem_originIdeal_iff', Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff]

theorem isIntegrallyClosed_of_absIntClosed' (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx0
  obtain ⟨p, hpm, hpx⟩ := hx0
  suffices H : ∀ n : ℕ, ∀ p : Polynomial T, p.Monic → p.natDegree = n →
      Polynomial.eval₂ (algebraMap T (FractionRing T)) x p = 0 →
      ∃ y, algebraMap T (FractionRing T) y = x from H _ p hpm rfl hpx
  intro n
  induction n with
  | zero =>
    intro p hp hd hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hd
    subst h1
    simp at hx
  | succ n ih =>
    intro p hp hd hx
    obtain ⟨r, hr⟩ := hT p hp (by omega)
    have hroot : p.IsRoot r := hr
    have hdec := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    set p' := p /ₘ (Polynomial.X - Polynomial.C r)
    have hp' : p'.Monic := (Polynomial.monic_X_sub_C r).of_mul_monic_left (by rw [hdec]; exact hp)
    have hd' : p'.natDegree = n := by
      have := congrArg Polynomial.natDegree hdec
      rw [(Polynomial.monic_X_sub_C r).natDegree_mul hp', Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hdec, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      exact (sub_eq_zero.mp h).symm
    · exact ih p' hp' hd' h

theorem exists_noetherian_model_of_mul_eq : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (b₁ c₁ : Localization.AtPrime Q) (s : T), s ≠ 0 →
      b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T),
      Function.Injective i ∧ IsLocalHom i ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 ∧ i sA = s ∧
        bA * cA = algebraMap A (Localization.AtPrime QA) sA ∧ jA bA = j b₁ := by
  classical
  intro T O _ _ _ _ _ _ _ _ hT E _ _ _ _ _ Q _ hQ j hj b₁ c₁ s hs0 hbc
  haveI : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed' T hT
  obtain ⟨⟨x, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b₁
  obtain ⟨⟨x', u'⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c₁
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul,
    IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q), ← map_mul,
    IsLocalization.eq_iff_exists Q.primeCompl] at hbc
  obtain ⟨v, hv⟩ := hbc
  obtain ⟨S, hsS, EA, _, _, _, e, hecomp, heinj, hrange⟩ :=
    exists_model E {x, x', (u : E), (u' : E), (v : E)} s
  letI : Algebra (loc S) EA :=
    ((algebraMap (Polynomial (loc S)) EA).comp (algebraMap (loc S) (Polynomial (loc S)))).toAlgebra
  haveI : IsScalarTower (loc S) (Polynomial (loc S)) EA := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hloc : IsLocalHom (loc S).subtype := ⟨fun a ha => isUnit_of_isUnit_coe S a ha⟩
  haveI := loc_isLocalRing S
  have hN : IsNoetherianRing (loc S) := by
    haveI := loc_isLocalization S
    exact IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)
  have hIC : IsIntegrallyClosed (loc S) := by
    haveI := loc_isLocalization S
    haveI := norm_isIntegrallyClosed S
    exact isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)
  have heA : ∀ a : loc S, e (algebraMap (loc S) EA a) = algebraMap T E a := by
    intro a
    change e (algebraMap (Polynomial (loc S)) EA (Polynomial.C a)) = _
    rw [← RingHom.comp_apply, hecomp, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      IsScalarTower.algebraMap_apply T (Polynomial T) E, Polynomial.algebraMap_apply]
    simp
  obtain ⟨xA, rfl⟩ := hrange x (by simp)
  obtain ⟨x'A, rfl⟩ := hrange x' (by simp)
  obtain ⟨uA, huA⟩ := hrange (u : E) (by simp)
  obtain ⟨u'A, hu'A⟩ := hrange (u' : E) (by simp)
  obtain ⟨vA, hvA⟩ := hrange (v : E) (by simp)
  let QA : Ideal EA := Q.comap e
  have hmemA : ∀ {w : EA} {w' : Q.primeCompl}, e w = (w' : E) → w ∈ QA.primeCompl := by
    intro w w' h
    change e w ∉ Q
    rw [h]; exact w'.2
  let sA : loc S := ⟨s, hsS⟩
  have hrel : vA * (xA * x'A) = vA * (algebraMap (loc S) EA sA * (uA * u'A)) := by
    apply heinj
    simp only [map_mul, heA, hvA, huA, hu'A]
    exact hv
  have horig : QA.comap (algebraMap (Polynomial (loc S)) EA) = GlobalTheory.KeyOriginCut.originIdeal (loc S) := by
    change (Q.comap e).comap _ = _
    rw [Ideal.comap_comap, hecomp, ← Ideal.comap_comap, hQ]
    exact comap_originIdeal' (loc S) T (loc S).subtype
  let jA : Localization.AtPrime QA →+* O := j.comp (Localization.localRingHom QA Q e rfl)
  have hjA : jA.comp (algebraMap (Polynomial (loc S)) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom (loc S).subtype) := by
    refine RingHom.ext fun y => ?_
    change j (Localization.localRingHom QA Q e rfl
      (algebraMap (Polynomial (loc S)) (Localization.AtPrime QA) y)) = _
    rw [IsScalarTower.algebraMap_apply (Polynomial (loc S)) EA (Localization.AtPrime QA),
      Localization.localRingHom_to_map, ← RingHom.comp_apply e, hecomp, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply j, hj]
    rfl
  refine ⟨loc S, inferInstance, inferInstance, inferInstance, hN, hIC, essFiniteType_loc S, (loc S).subtype,
    Subtype.val_injective, hloc, EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    QA, inferInstance, horig, jA, hjA,
    IsLocalization.mk' (Localization.AtPrime QA) xA ⟨uA, hmemA huA⟩,
    IsLocalization.mk' (Localization.AtPrime QA) x'A ⟨u'A, hmemA hu'A⟩, sA, ?_, rfl, ?_, ?_⟩
  · intro h
    exact hs0 (congrArg Subtype.val h)
  · rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul,
      IsScalarTower.algebraMap_apply (loc S) EA (Localization.AtPrime QA), ← map_mul,
      IsLocalization.eq_iff_exists QA.primeCompl]
    exact ⟨⟨vA, hmemA hvA⟩, hrel⟩
  · change j (Localization.localRingHom QA Q e rfl _) = _
    rw [Localization.localRingHom_mk']
    congr 2
    exact Subtype.ext huA

end GlobalTheory.VertUnitsNoeth
