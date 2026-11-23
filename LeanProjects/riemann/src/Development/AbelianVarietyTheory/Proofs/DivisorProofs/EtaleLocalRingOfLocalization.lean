import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem exists_finitePresentation_isLocalization_of_localization (A B E : Type) [CommRing A]
    [CommRing B] [CommRing E] [Algebra A B] (M : Submonoid A) [IsLocalization M B] [Algebra B E]
    [Algebra.FinitePresentation B E] :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra A D) (_ : Algebra.FinitePresentation A D)
      (φ : D →+* E), φ.comp (algebraMap A D) = (algebraMap B E).comp (algebraMap A B) ∧
      @IsLocalization D _ (Algebra.algebraMapSubmonoid D M) E _ φ.toAlgebra := by
  classical
  obtain ⟨n, f, hf, hK⟩ := ‹Algebra.FinitePresentation B E›
  letI : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B) :=
    MvPolynomial.algebraMvPolynomial
  haveI hL : IsLocalization (M.map (MvPolynomial.C (σ := Fin n))) (MvPolynomial (Fin n) B) :=
    MvPolynomial.isLocalization M B
  obtain ⟨s, hs⟩ := hK
  choose p hp using fun g : (s : Set (MvPolynomial (Fin n) B)) =>
    IsLocalization.surj (M.map (MvPolynomial.C (σ := Fin n))) (g : MvPolynomial (Fin n) B)
  let J₀ : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range fun g => (p g).1)
  have hJ : J₀.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)) =
      RingHom.ker f := by
    have hs' : Ideal.span (s : Set (MvPolynomial (Fin n) B)) = RingHom.ker f := hs
    rw [Ideal.map_span, ← hs']
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [← hp g]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span g.2)
    · rw [Ideal.span_le]
      intro g hg
      rw [SetLike.mem_coe, ← Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ (p ⟨g, hg⟩).2),
        hp ⟨g, hg⟩]
      exact Ideal.subset_span ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
  have hJfg : J₀.FG := Submodule.fg_span (Set.finite_range _)
  let D := MvPolynomial (Fin n) A ⧸ J₀
  haveI : Algebra.FinitePresentation A D := Algebra.FinitePresentation.quotient hJfg
  let Dl := MvPolynomial (Fin n) B ⧸ J₀.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B))
  haveI hDl : IsLocalization (Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n)))) Dl :=
    inferInstance
  let e : Dl ≃+* E := (Ideal.quotEquivOfEq hJ).trans (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv
  let φ : D →+* E := e.toRingHom.comp (algebraMap D Dl)
  refine ⟨D, inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩
  · ext a
    change e (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)
      (MvPolynomial.C a))) = algebraMap B E (algebraMap A B a)
    have he : ∀ x, e (Ideal.Quotient.mk _ x) = f x := fun x => rfl
    rw [he, MvPolynomial.algebraMap_def, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, f.commutes]
  · letI : Algebra D E := φ.toAlgebra
    let e' : Dl ≃ₐ[D] E := AlgEquiv.ofRingEquiv (f := e) (fun x => rfl)
    have hsub : Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n))) =
        Algebra.algebraMapSubmonoid D M := by
      ext x
      simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    haveI := IsLocalization.isLocalization_of_algEquiv
      (Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n)))) e'
    rwa [hsub] at this

theorem exists_etale_atPrime_algEquiv_of_isEtaleAt (R D : Type) [CommRing R] [CommRing D]
    [Algebra R D] [Algebra.FinitePresentation R D] (P' : Ideal D) [P'.IsPrime]
    [Algebra.IsEtaleAt R P'] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P') := by
  obtain ⟨f, hfP, hfet⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) P'
  let A' := Localization.Away f
  have hdisj : Disjoint (Submonoid.powers f : Set D) P' :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfP
  let q' : Ideal A' := P'.map (algebraMap D A')
  haveI hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) A' P' ‹_› hdisj
  have hcomap : q'.comap (algebraMap D A') = P' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) A' ‹_› hdisj
  haveI h1 : IsLocalization.AtPrime (Localization.AtPrime q') (q'.comap (algebraMap D A')) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f)
      (Localization.AtPrime q') q'
  haveI h2 : IsLocalization P'.primeCompl (Localization.AtPrime q') := by
    have h1' : IsLocalization (q'.comap (algebraMap D A')).primeCompl (Localization.AtPrime q') := h1
    have hsub : (q'.comap (algebraMap D A')).primeCompl = P'.primeCompl := by
      ext x
      simp only [Ideal.mem_primeCompl_iff, hcomap]
    rwa [hsub] at h1'
  let e : Localization.AtPrime q' ≃ₐ[D] Localization.AtPrime P' :=
    IsLocalization.algEquiv P'.primeCompl _ _
  exact ⟨A', inferInstance, inferInstance, hfet, q', hq', ⟨e.restrictScalars R⟩⟩

theorem essEtale_atPrime_of_etale_over_atPrime : ∀ (R A E : Type) [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] [Algebra (Localization.AtPrime q) E] [Algebra.Etale (Localization.AtPrime q) E] [Algebra R E] [IsScalarTower R (Localization.AtPrime q) E] (P : Ideal E) [P.IsPrime], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R A E _ _ _ _ _ q _ _ _ _ _ P _
  obtain ⟨D, _, _, _, φ, hφ, hloc⟩ :=
    exists_finitePresentation_isLocalization_of_localization A (Localization.AtPrime q) E q.primeCompl
  letI : Algebra R D := ((algebraMap A D).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FinitePresentation R D := Algebra.FinitePresentation.trans R A D
  letI : Algebra D E := φ.toAlgebra
  haveI : IsScalarTower R D E := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime q) E,
      IsScalarTower.algebraMap_eq R A (Localization.AtPrime q), ← RingHom.comp_assoc, ← hφ]
    rfl
  let EP := Localization.AtPrime P
  haveI : IsScalarTower D E EP := inferInstance
  haveI : IsScalarTower R D EP := inferInstance
  haveI hEP : IsLocalization.AtPrime EP (P.comap (algebraMap D E)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid D q.primeCompl) EP P
  let P' := P.comap (algebraMap D E)
  let eP : Localization.AtPrime P' ≃ₐ[D] EP := IsLocalization.algEquiv P'.primeCompl _ _
  haveI : Algebra.FormallyEtale R A := inferInstance
  haveI : Algebra.FormallyEtale A (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  haveI : Algebra.FormallyEtale R (Localization.AtPrime q) :=
    Algebra.FormallyEtale.comp R A (Localization.AtPrime q)
  haveI : Algebra.FormallyEtale R E := Algebra.FormallyEtale.comp R (Localization.AtPrime q) E
  haveI : Algebra.FormallyEtale E EP := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  haveI : Algebra.FormallyEtale R EP := Algebra.FormallyEtale.comp R E EP
  haveI : Algebra.IsEtaleAt R P' := Algebra.FormallyEtale.of_equiv (eP.restrictScalars R).symm
  obtain ⟨A', i1, i2, i3, q', i4, ⟨e⟩⟩ := exists_etale_atPrime_algEquiv_of_isEtaleAt R D P'
  exact ⟨A', i1, i2, i3, q', i4, ⟨e.trans (eP.restrictScalars R)⟩⟩

end GlobalTheory
