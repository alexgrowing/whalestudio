import Mathlib

open IsLocalRing in
private lemma finite_of_isFiniteLength {S : Type} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] {M : Type} [AddCommGroup M] [Module S M]
    (h : IsFiniteLength S M) : Finite M := by
  induction h with
  | of_subsingleton => exact Finite.of_subsingleton
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hIm : I = maximalIdeal S := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    haveI : Finite (S ⧸ maximalIdeal S) := ‹Finite (ResidueField S)›
    haveI : Finite (M ⧸ N) := Finite.of_equiv _ e.symm.toEquiv
    haveI : Finite (M ⧸ N.toAddSubgroup) := ‹Finite (M ⧸ N)›
    haveI : Finite N.toAddSubgroup := ih
    exact Finite.of_addSubgroup_quotient N.toAddSubgroup

open IsLocalRing in
theorem UpperTheory.monic_ideal_completion :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Finite (IsLocalRing.ResidueField O)] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
        [IsLocalHom (algebraMap O R)]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (J : Ideal R) (hJ : ∀ x : R, ∃ P : Polynomial O, P.Monic ∧ Polynomial.aeval x P ∈ J)
        (ϖ : O) (hϖ : Irreducible ϖ),
        Finite (R ⧸ (J ⊔ Ideal.span {algebraMap O R ϖ})) := by
  intro O R _ _ _ _ _ _ _ _ _ hres J hJ ϖ hϖ
  obtain ⟨I, hIdef⟩ : ∃ I, I = J ⊔ Ideal.span {algebraMap O R ϖ} := ⟨_, rfl⟩
  rw [← hIdef]
  have hJI : J ≤ I := hIdef ▸ le_sup_left
  have hϖI : algebraMap O R ϖ ∈ I :=
    hIdef ▸ (le_sup_right : _ ≤ J ⊔ Ideal.span {algebraMap O R ϖ}) (Ideal.subset_span rfl)
  by_cases hI : I = ⊤
  · subst hI
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Finite.of_subsingleton
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral O (R ⧸ I) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hx⟩ := hJ x
    refine ⟨P, hP, ?_⟩
    rw [← Polynomial.aeval_def]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O I) x P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJI hx)⟩
  have hm : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_zero_iff.mpr fun Q hQ =>
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) Q (by
      have hle : Ideal.span {ϖ} ≤ Q.comap (algebraMap O (R ⧸ I)) := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
        have : algebraMap O (R ⧸ I) ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hϖI
        rw [this]
        exact Q.zero_mem
      have hne : Q.comap (algebraMap O (R ⧸ I)) ≠ ⊤ := (Ideal.comap_isPrime _ Q).ne_top
      rw [← hm.eq_of_le hne hle]
      exact hm)
  haveI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
  have hImax : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hmk : ∀ x ∈ maximalIdeal R, Ideal.Quotient.mk I x ∈ maximalIdeal (R ⧸ I) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hz
    have h1 := hImax hz
    have h2 : x * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hx
    have h3 : (1 : R) ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem h2 h1
      simpa using this
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
  let φ : O →+* ResidueField (R ⧸ I) := (residue (R ⧸ I)).comp (algebraMap O (R ⧸ I))
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres x
    refine ⟨a, ?_⟩
    have h := hmk _ ha
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at h
    exact h.symm
  have hφk : ∀ a ∈ maximalIdeal O, φ a = 0 := by
    intro a ha
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hu => ha (isUnit_of_map_unit (algebraMap O R) a hu)
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hmk _ h1)
  haveI : Finite (O ⧸ maximalIdeal O) := ‹Finite (ResidueField O)›
  haveI : Finite (ResidueField (R ⧸ I)) :=
    Finite.of_surjective (Ideal.Quotient.lift (maximalIdeal O) φ hφk)
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hφs)
  exact finite_of_isFiniteLength (S := R ⧸ I) (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
