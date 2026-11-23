import Mathlib
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
namespace GlobalTheory.GaloisPowerRoots

theorem isLocalRing_of_isInvariant {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [hH : HenselianLocalRing A] :
    IsLocalRing B := by
  classical
  cases nonempty_fintype G
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal B
  have hunder : ∀ P : Ideal B, P.IsMaximal → P.under A = maximalIdeal A := fun P hP =>
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
  suffices hs : ∀ σ : G, σ • Q = Q by
    refine IsLocalRing.of_unique_max_ideal ⟨Q, hQ, fun P hP => ?_⟩
    haveI := hP.isPrime
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q P
      ((hunder Q hQ).trans (hunder P hP).symm)
    rw [hg, hs]
  have hmax : ∀ σ : G, (σ • Q).IsMaximal := fun σ => by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_equiv _
  have hb : ∀ σ : G, ∃ b : B, b - 1 ∈ Q ∧ (σ • Q ≠ Q → b ∈ σ • Q) := by
    intro σ
    by_cases h : σ • Q = Q
    · exact ⟨1, by simp, fun h' => (h' h).elim⟩
    · have := (hmax σ).coprime_of_ne hQ h
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp this)
      refine ⟨x, ?_, fun _ => hx⟩
      have : x - 1 = -y := by rw [← hxy]; ring
      rw [this]; exact Q.neg_mem hy
  choose b hb1 hb2 using hb
  let φ := Ideal.Quotient.mk Q
  have hφ1 : ∀ x : B, x - 1 ∈ Q ↔ φ x = 1 := fun x => by
    rw [← map_one φ, Ideal.Quotient.eq]
  have hφ0 : ∀ x : B, x ∈ Q ↔ φ x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem.symm
  set β := ∏ σ : G, b σ with hβ
  have hβ1 : β - 1 ∈ Q := by
    rw [hφ1, hβ, map_prod]
    exact Finset.prod_eq_one fun σ _ => (hφ1 _).mp (hb1 σ)
  have hβ2 : ∀ σ : G, σ • Q ≠ Q → σ • β ∈ Q := by
    intro σ hσ
    have h1 : σ⁻¹ • Q ≠ Q := fun h => hσ (by rw [← h, smul_inv_smul, h])
    rw [← Ideal.mem_inv_pointwise_smul_iff]
    exact Ideal.prod_mem _ (Finset.mem_univ σ⁻¹) (hb2 _ h1)
  let H := MulAction.stabilizer G Q
  set γ := ∏ h : H, (h : G) • β with hγ
  have hγ1 : φ γ = 1 := by
    rw [hγ, map_prod]
    refine Finset.prod_eq_one fun h _ => (hφ1 _).mp ?_
    have h2 : (h : G) • Q = Q := h.2
    have := Ideal.smul_mem_pointwise_smul (h : G) _ _ hβ1
    rwa [h2, smul_sub, smul_one] at this
  have hγ2 : ∀ σ : G, σ • Q = Q → σ • γ = γ := fun σ hσ =>
    Finset.smul_prod_perm (G := H) β ⟨σ, hσ⟩
  have hγ3 : ∀ σ : G, σ • Q ≠ Q → φ (σ • γ) = 0 := by
    intro σ hσ
    rw [← hφ0, hγ, Finset.smul_prod']
    refine Ideal.prod_mem _ (Finset.mem_univ (1 : H)) ?_
    simpa using hβ2 σ hσ
  let O : Finset B := Finset.univ.image fun σ : G => σ • γ
  have hγO : γ ∈ O := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, one_smul _ _⟩
  have hO : ∀ δ ∈ O.erase γ, φ δ = 0 := by
    intro δ hδ
    obtain ⟨hne, hδ⟩ := Finset.mem_erase.mp hδ
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hδ
    exact hγ3 σ fun h => hne (hγ2 σ h)
  set f : B[X] := ∏ δ ∈ O, (X - C δ) with hf
  have hfm : f.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hfinv : ∀ σ : G, σ • f = f := by
    intro σ
    rw [hf, Finset.smul_prod']
    simp only [smul_sub, smul_X, smul_C]
    refine Finset.prod_nbij' (fun δ => σ • δ) (fun δ => σ⁻¹ • δ) ?_ ?_ ?_ ?_ ?_
    · intro δ hδ
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hδ
      exact Finset.mem_image.mpr ⟨σ * τ, Finset.mem_univ _, mul_smul _ _ _⟩
    · intro δ hδ
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hδ
      exact Finset.mem_image.mpr ⟨σ⁻¹ * τ, Finset.mem_univ _, mul_smul _ _ _⟩
    · intro δ _; simp
    · intro δ _; simp
    · intro δ _; rfl
  have hlift : f ∈ Polynomial.lifts (algebraMap A B) :=
    f.lifts_iff_coeff_lifts.mpr fun n =>
      Algebra.IsInvariant.isInvariant (G := G) _ fun σ => by rw [← coeff_smul, hfinv]
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hfm
  have hfφ : f.map φ = (X - 1) * X ^ (O.erase γ).card := by
    rw [hf, ← Finset.mul_prod_erase O _ hγO, Polynomial.map_mul, Polynomial.map_prod,
      ← Finset.prod_const]
    congr 1
    · simp [hγ1]
    · refine Finset.prod_congr rfl fun δ hδ => ?_
      simp [hO δ hδ]
  have hmem : ∀ a : A, a ∈ maximalIdeal A ↔ φ (algebraMap A B a) = 0 := fun a => by
    rw [← hunder Q hQ, ← hφ0]; rfl
  have hev : ∀ q : A[X], φ (algebraMap A B (q.eval 1)) = ((q.map (algebraMap A B)).map φ).eval 1 :=
    fun q => by rw [eval_one_map, eval_one_map]
  haveI : Nontrivial (B ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  obtain ⟨a, ha1, ha2⟩ := hH.is_henselian p hp2 1
    (by rw [hmem, hev, hp1, hfφ]; simp)
    (by
      rw [← notMem_maximalIdeal, hmem, hev, ← derivative_map, ← derivative_map, hp1, hfφ]
      simp)
  have ha3 : φ (algebraMap A B a) = 1 := by
    rw [hmem, map_sub, map_sub, map_one, map_one, sub_eq_zero] at ha2
    exact ha2
  have ha4 : f.eval (algebraMap A B a) = 0 := by
    rw [← hp1, eval_map_algebraMap, aeval_algebraMap_apply, coe_aeval_eq_eval, ha1.eq_zero, map_zero]
  rw [hf, eval_prod, Finset.prod_eq_zero_iff] at ha4
  obtain ⟨δ, hδ, hδ2⟩ := ha4
  have hδ3 : algebraMap A B a = δ := by simpa [sub_eq_zero] using hδ2
  have hδ4 : δ = γ := by
    by_contra hne
    have := hO δ (Finset.mem_erase.mpr ⟨hne, hδ⟩)
    rw [← hδ3, ha3] at this
    exact one_ne_zero this
  intro σ
  by_contra hσ
  have := hγ3 σ hσ
  rw [← hδ4, ← hδ3, smul_algebraMap, ha3] at this
  exact one_ne_zero this

theorem exists_sub_mem_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    [IsAlgClosed (ResidueField A)] (t : B) :
    ∃ a : A, t - algebraMap A B a ∈ maximalIdeal B := by
  haveI : IsLocalHom (algebraMap A B) := inferInstance
  have hint : (ResidueField.map (algebraMap A B)).IsIntegral := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    obtain ⟨p, hp, hp2⟩ := Algebra.IsIntegral.isIntegral (R := A) y
    refine ⟨p.map (residue A), hp.map _, ?_⟩
    rw [eval₂_map, ResidueField.map_comp_residue, ← hom_eval₂, hp2, map_zero]
  obtain ⟨x, hx⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral _ hint).2 (residue B t)
  obtain ⟨a, rfl⟩ := residue_surjective x
  refine ⟨a, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.map_residue, sub_self]

theorem exists_unit_mul_pow {R : Type*} (K L : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosure R L)] :
    ∃ (u : (integralClosure R L)ˣ) (ϖ : integralClosure R L),
      algebraMap R _ π = u * ϖ ^ Module.finrank K L := by
  set S := integralClosure R L
  haveI : FaithfulSMul R L := FaithfulSMul.trans R K L
  haveI : FaithfulSMul R S := FaithfulSMul.tower_bot R S L
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain R K L
  haveI : Module.Finite R S := IsIntegralClosure.finite R K L S
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  have hp0 : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hnf : ¬ IsField S := fun h => IsDiscreteValuationRing.not_isField R
    ((Algebra.IsIntegral.isField_iff_isField (FaithfulSMul.algebraMap_injective R S)).mpr h)
  haveI : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 0 2).mpr (inferInstance : IsDedekindDomain S)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hπ0 : algebraMap R S π ≠ 0 := by simpa using hπ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hϖ
  refine ⟨u, ϖ, ?_⟩
  have h1 := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0
  have h2 : (maximalIdeal R).inertiaDeg' (maximalIdeal S) = 1 := by
    rw [Ideal.inertiaDeg'_algebraMap]
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    letI : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
    refine Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨RingHom.injective _, fun x => ?_⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := exists_sub_mem_maximalIdeal (A := R) t
    exact ⟨Ideal.Quotient.mk _ a, (Ideal.Quotient.eq.mpr ha).symm⟩
  have hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S ^ e := by
    rw [hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu,
      Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  have h3 : Ideal.ramificationIdx' (maximalIdeal R) (maximalIdeal S) = e := by
    refine Ideal.ramificationIdx'_spec hmap.le ?_
    rw [hmap]
    exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) e).not_ge
  rw [h2, h3, mul_one] at h1
  rw [← h1, hu]

theorem exists_pow_eq_of_isGalois {R : Type*} (K L M : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (hn : IsUnit (Module.finrank K L : R))
    [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K M]
    [FiniteDimensional K M] (ρ : M)
    (hρ : ρ ^ Module.finrank K L = algebraMap K M (algebraMap R K π)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra R M := ((algebraMap K M).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply K L M (algebraMap R K x)
  set n := Module.finrank K L with hn'
  have hn0 : 0 < n := Module.finrank_pos
  set T := integralClosure R M
  set S := integralClosure R L
  haveI : FaithfulSMul R M := FaithfulSMul.trans R K M
  haveI : FaithfulSMul R T := FaithfulSMul.tower_bot R T M
  haveI : Algebra.IsInvariant R T (M ≃ₐ[K] M) := ⟨fun x hx => by
    have h1 : (x : M) ∈ (⊥ : IntermediateField K M) :=
      (IsGalois.mem_bot_iff_fixed _).mpr fun σ => congrArg Subtype.val (hx σ)
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp h1
    have h2 : IsIntegral R z := by
      rw [← isIntegral_algebraMap_iff (algebraMap K M).injective, hz]; exact x.2
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    refine ⟨r, Subtype.ext ?_⟩
    rw [← hz, ← hr]; rfl⟩
  haveI : IsLocalRing T := isLocalRing_of_isInvariant (A := R) (G := M ≃ₐ[K] M)
  let ι : S →+* T := ((algebraMap L M).comp (algebraMap S L)).codRestrict
    T.toSubring (fun x => (x.2 : IsIntegral R (x : L)).algebraMap)
  have hι : ∀ x : S, ((ι x : T) : M) = algebraMap L M x := fun _ => rfl
  have hunit : ∀ x : S, IsUnit (ι x) → IsUnit x := by
    intro x hx
    obtain ⟨z, hz⟩ := hx.exists_right_inv
    have hz' : algebraMap L M x * (z : M) = 1 := congrArg Subtype.val hz
    have hx0 : (x : L) ≠ 0 := fun h => by simp [h] at hz'
    have h3 : algebraMap L M (x : L)⁻¹ = z := by
      rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hz'
    have h4 : IsIntegral R (x : L)⁻¹ := by
      rw [← isIntegral_algebraMap_iff (algebraMap L M).injective, h3]; exact z.2
    exact IsUnit.of_mul_eq_one (⟨_, h4⟩ : S) (Subtype.ext (mul_inv_cancel₀ hx0))
  haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ι x) with h | h
    · exact Or.inl (hunit _ h)
    · exact Or.inr (hunit _ (by simpa using h))
  obtain ⟨u, ϖ, hu⟩ := exists_unit_mul_pow K L hπ
  have hu' : algebraMap K L (algebraMap R K π) = ((u : S) : L) * (ϖ : L) ^ n :=
    congrArg Subtype.val hu
  have hπ0 : algebraMap K L (algebraMap R K π) ≠ 0 := by simpa using hπ.ne_zero
  have hϖ0 : (ϖ : L) ≠ 0 := fun h => hπ0 (by rw [hu', h, zero_pow hn0.ne', mul_zero])
  have hϖ1 : algebraMap L M ϖ ≠ 0 := by simpa using hϖ0
  have hy : (ρ / algebraMap L M ϖ) ^ n = (ι u : T) := by
    rw [div_pow, hρ, IsScalarTower.algebraMap_apply K L M, hu', hι, map_mul, map_pow]
    field_simp
  have hyint : IsIntegral R (ρ / algebraMap L M ϖ) :=
    IsIntegral.of_pow hn0 (by rw [hy]; exact (ι u).2)
  set y : T := ⟨_, hyint⟩ with hydef
  have hyn : y ^ n = ι u := Subtype.ext hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0.ne').mp (by rw [hyn]; exact u.isUnit.map ι)
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  haveI : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have hfix : ∀ σ : M ≃ₐ[L] M, σ (y : M) = y := by
    intro σ
    let τ : M ≃ₐ[K] M := σ.restrictScalars K
    obtain ⟨a, ha⟩ := exists_sub_mem_maximalIdeal (A := R) y
    have ha2 : τ • y - algebraMap R T a ∈ maximalIdeal T := by
      rw [← smul_algebraMap τ a, ← smul_sub]
      intro h
      apply ha
      have := h.map (MulSemiringAction.toRingHom _ T τ⁻¹)
      rwa [MulSemiringAction.toRingHom_apply, inv_smul_smul] at this
    have hres : residue T (τ • y) = residue T y := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      simpa using (maximalIdeal T).sub_mem ha2 ha
    have hpow : (τ • y) ^ n = y ^ n := by
      rw [← smul_pow', hyn]
      exact Subtype.ext (σ.commutes _)
    have h5 := geom_sum₂_mul (τ • y) y n
    rw [hpow, sub_self, mul_eq_zero] at h5
    rcases h5 with h5 | h5
    · exfalso
      have h6 := congrArg (residue T) h5
      simp only [map_sum, map_mul, map_pow, hres, map_zero] at h6
      rw [geom_sum₂_self] at h6
      have h7 : IsUnit ((n : ResidueField T) * residue T y ^ (n - 1)) := by
        refine IsUnit.mul ?_ ((hyu.map _).pow _)
        simpa using (hn.map (algebraMap R T)).map (residue T)
      exact h7.ne_zero h6
    · exact congrArg Subtype.val (sub_eq_zero.mp h5)
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hfix)
  refine ⟨z * ϖ, (algebraMap L M).injective ?_⟩
  rw [map_pow, map_mul, hz, ← IsScalarTower.algebraMap_apply K L M, ← hρ]
  congr 1
  exact div_mul_cancel₀ _ hϖ1

theorem exists_pow_eq_of_tower {R : Type*} (K L E F : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (hn : IsUnit (Module.finrank K L : R))
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [FiniteDimensional K E]
    [Field F] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [IsGalois K F] (ρ : E)
    (hρ : ρ ^ Module.finrank K L = algebraMap K E (algebraMap R K π)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  let M := IntermediateField.normalClosure K E F
  letI : Algebra L M := ((algebraMap E M).comp (algebraMap L E)).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K E M, IsScalarTower.algebraMap_apply K L E]; rfl
  refine exists_pow_eq_of_isGalois K L M hH hπ hn (algebraMap E M ρ) ?_
  rw [← map_pow, hρ, ← IsScalarTower.algebraMap_apply]

theorem exists_pow_finrank_eq {R : Type} (K : Type u_1) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hn : IsUnit (Module.finrank K L : R)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  let F := SeparableClosure L
  haveI : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K L F
  haveI : IsSepClosure K F := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K F := inferInstance
  haveI : NeZero ((Module.finrank K L : ℕ) : F) := ⟨by
    simpa using ((hn.map (algebraMap R K)).map (algebraMap K F)).ne_zero⟩
  obtain ⟨ρ, hρ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K F (algebraMap R K π))
    (Module.finrank K L)
  let E := IntermediateField.adjoin L {ρ}
  haveI : FiniteDimensional L E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ρ)
  haveI : FiniteDimensional K E := Module.Finite.trans L E
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_pow_eq_of_tower K L E F hH hπ hn
    ⟨ρ, IntermediateField.mem_adjoin_simple_self L ρ⟩ (Subtype.ext hρ)

end GlobalTheory.GaloisPowerRoots
