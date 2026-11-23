import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfieldStatement
open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.FibreRetract

theorem exists_section_mod (T O : Type) [CommRing T] [IsLocalRing T] [HenselianLocalRing T]
    [IsAlgClosed (ResidueField T)] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [IsLocalHom (algebraMap T O)] (I : Ideal O) (hI : I ≠ ⊤)
    (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T) [IsLocalHom i]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] (b : B →+* O ⧸ I)
    (hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i) :
    ∃ s : B →+* T, s.comp (algebraMap A B) = i ∧
      ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp s = b := by
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (O ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (O ⧸ I) := GlobalTheory.henselianLocalRing_of_finite O (O ⧸ I)
  set π : T →+* O ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap T O) with hπ
  haveI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hI)
  haveI : IsLocalHom π := inferInstance
  have het : (algebraMap A B).Etale := RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield A B (ResidueField T) (ResidueField (O ⧸ I))
    ((residue T).comp i) (ResidueField.map π) ((residue (O ⧸ I)).comp b)
    (fun a ha => by
      simp only [RingHom.comp_apply, residue_eq_zero_iff]
      exact map_nonunit i a ha)
    (by
      ext a
      have := DFunLike.congr_fun hb a
      simp only [RingHom.comp_apply] at this ⊢
      rw [this, ResidueField.map_residue])
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.NCyc.StrictLocLift.lift_exists (algebraMap A B) het i ψ hψ1
  refine ⟨s, hs1, ?_⟩
  refine GlobalTheory.NCyc.StrictLocLift.lift_unique (algebraMap A B) het (π.comp i) _ _ ?_ hb ?_
  · rw [RingHom.comp_assoc, hs1]
  · ext x
    have h2 := DFunLike.congr_fun hψ2 x
    have h3 := DFunLike.congr_fun hs2 x
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [← h2, ← h3, ResidueField.map_residue]

end GlobalTheory.FibreRetract

namespace GlobalTheory.FibreRetract

theorem fibre_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (j : EA →+* O),
      j.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T) (e : EA →+* A₁),
      Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      e.comp (algebraMap (Polynomial A) EA) = f.comp (Polynomial.evalRingHom 0) ∧
      ∀ x : EA, algebraMap T O (i₁ (e x)) - j x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X} := by
  intro T O _ _ _ _ _ _ _ _ hT hTO ht A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ j hj
  obtain ⟨hTh, hTac, -⟩ := GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X} with hIdef
  have hI : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp
    (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr ht))
  letI : Algebra (Polynomial A) A := (Polynomial.evalRingHom 0).toAlgebra
  let B := TensorProduct (Polynomial A) A EA
  have hC : ∀ c : T, algebraMap (Polynomial T) O (Polynomial.C c) = algebraMap T O c := fun c => by
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O c, Polynomial.algebraMap_eq]
  let φ : Polynomial A →+* O ⧸ I :=
    (Ideal.Quotient.mk I).comp ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i))
  letI : Algebra (Polynomial A) (O ⧸ I) := φ.toAlgebra
  let f₁ : A →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i
      commutes' := fun p => by
        change Ideal.Quotient.mk I (algebraMap T O (i (p.eval 0))) =
          Ideal.Quotient.mk I (algebraMap (Polynomial T) O (p.map i))
        rw [Ideal.Quotient.eq]
        obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p.map i)
        have h0 : (p.map i).coeff 0 = i (p.eval 0) := by
          rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
        rw [h0] at hq
        rw [← hC, ← map_sub, ← neg_sub, hq, map_neg, map_mul]
        exact I.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) }
  let f₂ : EA →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp j
      commutes' := fun p => by
        change Ideal.Quotient.mk I (j (algebraMap (Polynomial A) EA p)) = φ p
        have := DFunLike.congr_fun hj p
        simp only [RingHom.comp_apply] at this
        simp only [φ, RingHom.comp_apply, this, Polynomial.coe_mapRingHom] }
  let b : B →+* O ⧸ I := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i := by
    ext a
    change b (algebraMap A B a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    exact (Algebra.TensorProduct.lift_tmul f₁ f₂ _ a 1).trans (by rw [map_one, mul_one]; rfl)
  haveI := hTh; haveI := hTac
  obtain ⟨s, hs1, hs2⟩ := exists_section_mod T O I hI A i B b hb
  let P : Ideal B := (maximalIdeal T).comap s
  haveI hP : P.IsPrime := Ideal.comap_isPrime s (maximalIdeal T)
  let A₁ := Localization.AtPrime P
  have hunit : ∀ y : P.primeCompl, IsUnit (s y) := fun y => by
    have hy : (y : B) ∉ P := y.2
    by_contra h
    exact hy ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let i₁ : A₁ →+* T := IsLocalization.lift hunit
  have hi₁ : i₁.comp (algebraMap B A₁) = s := IsLocalization.lift_comp hunit
  let f : A →+* A₁ := algebraMap A A₁
  let e : EA →+* A₁ := (algebraMap B A₁).comp
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] B).toRingHom
  obtain ⟨hdom, hic⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A P A₁
  haveI := hdom
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsNoetherianRing A₁ := IsLocalization.isNoetherianRing P.primeCompl A₁ inferInstance
  haveI : Algebra.EssFiniteType ℤ B := Algebra.EssFiniteType.comp ℤ A B
  haveI : Algebra.EssFiniteType B A₁ := Algebra.EssFiniteType.of_isLocalization A₁ P.primeCompl
  haveI : Algebra.EssFiniteType ℤ A₁ := Algebra.EssFiniteType.comp ℤ B A₁
  have hcomp : i₁.comp f = i := by
    rw [show f = (algebraMap B A₁).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B A₁,
      ← RingHom.comp_assoc, hi₁, hs1]
  have hloc : IsLocalHom i₁ := ⟨fun x hx => by
    obtain ⟨⟨b', y⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have h1 : i₁ (IsLocalization.mk' A₁ b' y) * s y = s b' := by
      rw [← hi₁, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have h2 : IsUnit (s b') := h1 ▸ hx.mul (hunit y)
    intro hb'
    exact (IsLocalRing.mem_maximalIdeal _).mp hb' h2⟩
  haveI : Algebra.QuasiFinite A B := inferInstance
  haveI : Algebra.QuasiFinite A A₁ := inferInstance
  have hinj : Function.Injective i₁ := by
    have h1 : (RingHom.ker i₁).comap f = ⊥ := by
      rw [RingHom.comap_ker, hcomp]; exact (RingHom.injective_iff_ker_eq_bot i).mp hi
    have h2 : (⊥ : Ideal A₁).comap f = ⊥ := eq_bot_iff.mpr fun a ha => h1 ▸ Ideal.comap_mono bot_le ha
    haveI : (RingHom.ker i₁).IsPrime := RingHom.ker_isPrime i₁
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) (⊥ : Ideal A₁) (RingHom.ker i₁) bot_le
      (by rw [Ideal.under, Ideal.under]; exact h2.trans h1.symm)
    exact (RingHom.injective_iff_ker_eq_bot i₁).mpr this.symm
  refine ⟨A₁, inferInstance, hdom, inferInstance, inferInstance, hic, ?_, f, i₁, e, hinj,
    hloc, hcomp, ?_, fun x => ?_⟩
  · convert ‹Algebra.EssFiniteType ℤ A₁› using 1
    exact Subsingleton.elim _ _
  · refine RingHom.ext fun p => ?_
    change algebraMap B A₁ (Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) EA p)) =
      algebraMap A A₁ (p.eval 0)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B A₁]
    rfl
  · have h3 := DFunLike.congr_fun hs2 (Algebra.TensorProduct.includeRight x)
    have h4 : i₁ (e x) = s (Algebra.TensorProduct.includeRight x) := by
      rw [← hi₁]; rfl
    rw [h4]
    apply Ideal.Quotient.eq.mp
    refine h3.trans ?_
    change Algebra.TensorProduct.lift f₁ f₂ _ ((1 : A) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

end GlobalTheory.FibreRetract
