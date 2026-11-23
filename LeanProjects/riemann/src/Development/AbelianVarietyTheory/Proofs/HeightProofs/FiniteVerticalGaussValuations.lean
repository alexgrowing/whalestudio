import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.SemistableReduction.AlgAll

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

namespace VerticalGauss

open IsLocalRing IsDedekindDomain

noncomputable def extPrime {K : Type} [Field K] [NumberField K] (σ : Type)
    (la : HeightOneSpectrum (𝓞 K)) : Ideal (MvPolynomial σ (𝓞 K)) :=
  la.asIdeal.map MvPolynomial.C

theorem mem_extPrime {K : Type} [Field K] [NumberField K] {σ : Type}
    (la : HeightOneSpectrum (𝓞 K)) (p : MvPolynomial σ (𝓞 K)) :
    p ∈ extPrime σ la ↔ ∀ m, p.coeff m ∈ la.asIdeal :=
  MvPolynomial.mem_map_C_iff

instance extPrime_isPrime {K : Type} [Field K] [NumberField K] (σ : Type)
    (la : HeightOneSpectrum (𝓞 K)) : (extPrime σ la).IsPrime := by
  haveI := la.isPrime
  unfold extPrime
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) la.asIdeal).symm.toMulEquiv.isDomain

theorem isDVR {K : Type} [Field K] [NumberField K] (σ : Type) [Finite σ]
    (la : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime (extPrime σ la)) := by
  classical
  set P := extPrime σ la
  set Ol := Localization.AtPrime la.asIdeal
  have : IsDiscreteValuationRing Ol :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot Ol
  have hC : ∀ y : la.asIdeal.primeCompl,
      IsUnit ((algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)).comp
        (MvPolynomial.C) (y : 𝓞 K)) := by
    intro y
    apply IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P)
      ⟨MvPolynomial.C (y : 𝓞 K), _⟩
    intro hy
    apply y.2
    have := (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := MvPolynomial.C (y : 𝓞 K))).mp hy 0
    simpa using this
  let φ : Ol →+* Localization.AtPrime P := IsLocalization.lift (M := la.asIdeal.primeCompl) hC
  have hφ : φ.comp (algebraMap (𝓞 K) Ol) =
      (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)).comp MvPolynomial.C :=
    IsLocalization.lift_comp hC
  have hmax : maximalIdeal (Localization.AtPrime P) = (maximalIdeal Ol).map φ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, hφ, ← Ideal.map_map]
    rfl
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    intro h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
    have hm : (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)) (MvPolynomial.C a) ∈
        P.map (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    rw [h, Ideal.mem_bot] at hm
    have hinj := IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl)
      P.primeCompl_le_nonZeroDivisors
    apply ha0
    have := hinj (hm.trans (map_zero _).symm)
    simpa using this
  refine ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 4).mpr ?_
  rw [hmax]
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Ol))
  rw [hg]
  refine ⟨⟨φ g, ?_⟩⟩
  change Ideal.map φ (Ideal.span {g}) = Ideal.span {φ g}
  rw [Ideal.map_span, Set.image_singleton]

theorem injective_of_dvr {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] (φ : R →+* Ω)
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hker : ∀ r, φ r = 0 → r ∈ P) (a : R) (ha : a ∈ P) (ha0 : φ a ≠ 0) :
    Function.Injective φ := by
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (hker _ h)
  let ψ : Localization.AtPrime P →+* Ω := IsLocalization.lift (M := P.primeCompl) hu
  have hψ : ∀ r, ψ (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  have hϖ0 : ψ ϖ ≠ 0 := by
    intro h
    have hm : algebraMap R (Localization.AtPrime P) a ∈ maximalIdeal (Localization.AtPrime P) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P a).2 ha
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    apply ha0
    rw [← hψ, hc, map_mul, h, zero_mul]
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hinj := IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  have hr1 : algebraMap R (Localization.AtPrime P) r ≠ 0 := (map_ne_zero_iff _ hinj).2 hr0
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr1 hϖ
  rw [← hψ, hn, map_mul, map_pow] at hr
  exact mul_ne_zero (u.isUnit.map ψ).ne_zero (pow_ne_zero _ hϖ0) hr

theorem nonneg_of_isIntegral {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (w : AddValuation Ω (WithTop ℤ)) (h : ∀ r, 0 ≤ w (algebraMap R Ω r)) {b : Ω}
    (hb : IsIntegral R b) : 0 ≤ w b := by
  letI : Algebra R (vRing w) := ((algebraMap R Ω).codRestrict (vRing w) h).toAlgebra
  haveI : IsScalarTower R (vRing w) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  rw [← hy]
  exact y.2

theorem finite_places {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower R (FractionRing R) Ω]
    [FiniteDimensional (FractionRing R) Ω]
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)] :
    {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ x : R, 0 ≤ v (algebraMap R Ω x) ∧ (0 < v (algebraMap R Ω x) ↔ x ∈ P)}.Finite := by
  set O := Localization.AtPrime P
  set F := FractionRing R
  letI : Algebra O Ω := ((algebraMap F Ω).comp (algebraMap O F)).toAlgebra
  haveI : IsScalarTower O F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R O Ω := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply O F Ω, ← IsScalarTower.algebraMap_apply R O F,
      ← IsScalarTower.algebraMap_apply R F Ω])
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  obtain ⟨hD, _, _, _, hmax, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F Ω
  haveI : IsFractionRing (integralClosure O Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension F Ω
  haveI := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure O Ω)) := by
    refine Finite.of_injective (fun v => (⟨v.asIdeal, v.isMaximal⟩ :
      {I : Ideal (integralClosure O Ω) | I.IsMaximal})) ?_
    intro v v' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  obtain ⟨e, -⟩ := ValPl.placesOver_bij O F Ω
  have hfin : (ValPl.PlacesOver O Ω).Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
  refine hfin.subset ?_
  rintro v ⟨h1, h2⟩
  exact ⟨h1, (ValPl.placesOver_iff_loc P v).1 h2⟩

end VerticalGauss

open VerticalGauss IsDedekindDomain in

theorem finite_vertical_gauss_valuations : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D : ℕ) (x : Fin D → Ω), (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧ v g ≠ 0 ∧ ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∀ p : MvPolynomial (Fin D) (𝓞 K), 0 ≤ v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ∧ (0 < v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ↔ ∀ m, p.coeff m ∈ la.asIdeal)}.Finite := by
  intro K Ω _ _ _ _ D x hFG htr g hg
  classical
  by_contra hinf
  obtain ⟨v₀, -, -, la₀, h₀⟩ := Set.Infinite.nonempty hinf
  apply hinf
  clear hinf
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let ι : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hι : Function.Injective ι :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let φ : MvPolynomial (Fin D) (𝓞 K) →+* Ω := MvPolynomial.eval₂Hom ι x
  have hinj : Function.Injective φ := by
    haveI := isDVR (Fin D) la₀
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la₀.ne_bot
    refine injective_of_dvr φ (extPrime (Fin D) la₀) (fun r hr => ?_) (MvPolynomial.C a)
      (Ideal.mem_map_of_mem _ ha) ?_
    · rw [mem_extPrime, ← (h₀ r).2]
      change 0 < v₀ (φ r)
      rw [hr]; simp
    · simp only [φ, MvPolynomial.eval₂Hom_C]
      exact (map_ne_zero_iff _ hι).2 ha0
  letI : Algebra (𝓞 K) Ω := ι.toAlgebra
  haveI : IsScalarTower (𝓞 K) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (𝓞 K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hι
  have hind : AlgebraicIndependent (𝓞 K) x := hinj
  haveI : Algebra.IsAlgebraic (𝓞 K) K := IsLocalization.isAlgebraic K (nonZeroDivisors (𝓞 K))
  have hB : IsTranscendenceBasis K x :=
    (hind.extendScalars K).isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  have hB' : IsTranscendenceBasis (𝓞 K) x :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_iff (𝓞 K) K).2 hB
  set R := MvPolynomial (Fin D) (𝓞 K)
  letI : Algebra R Ω := φ.toAlgebra
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI halg : Algebra.IsAlgebraic R Ω := by
    have := hB'.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq hind.aevalEquiv.toRingEquiv.toRingHom
      (RingHom.id Ω) hind.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hind.algebraMap_aevalEquiv p)
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω := Algebra.IsAlgebraic.extendScalars
    (IsFractionRing.injective R (FractionRing R))
  haveI : FiniteDimensional (FractionRing R) Ω := by
    obtain ⟨S, hS⟩ := hFG
    have htop : IntermediateField.adjoin (FractionRing R) (S : Set Ω) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
      have hO : ∀ a : 𝓞 K, ι a ∈ IntermediateField.adjoin (FractionRing R) (S : Set Ω) := by
        intro a
        have : ι a = algebraMap (FractionRing R) Ω (algebraMap R _ (MvPolynomial.C a)) := by
          rw [← IsScalarTower.algebraMap_apply]
          exact (MvPolynomial.eval₂Hom_C ι x a).symm
        rw [this]; exact IntermediateField.algebraMap_mem _ _
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
      | algebraMap k =>
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
        rw [map_div₀]
        exact div_mem (hO a) (hO b)
      | add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)
      | inv a _ ha => exact inv_mem (ha trivial)
      | mul a b _ _ ha hb => exact mul_mem (ha trivial) (hb trivial)
    have : FiniteDimensional (FractionRing R)
        (IntermediateField.adjoin (FractionRing R) (S : Set Ω)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ =>
        (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    rw [htop] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  obtain ⟨r, hr0, hr⟩ := (halg.isAlgebraic g).exists_integral_multiple
  obtain ⟨s, hs0, hs⟩ := (halg.isAlgebraic g⁻¹).exists_integral_multiple
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 (mul_ne_zero hr0 hs0)
  have hfin : {la : HeightOneSpectrum (𝓞 K) |
      la.asIdeal ∣ Ideal.span {MvPolynomial.coeff m (r * s)}}.Finite :=
    Ideal.finite_factors (by simpa using hm)
  refine (hfin.biUnion (t := fun la => {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ y : R, 0 ≤ v (algebraMap R Ω y) ∧ (0 < v (algebraMap R Ω y) ↔ y ∈ extPrime (Fin D) la)})
      (fun la _ => haveI := isDVR (Fin D) la; finite_places _)).subset ?_
  rintro v ⟨hv, hvg, la, hla⟩
  have hla' : ∀ y : R, 0 ≤ v (algebraMap R Ω y) ∧
      (0 < v (algebraMap R Ω y) ↔ y ∈ extPrime (Fin D) la) := fun y => by
    rw [mem_extPrime]; exact hla y
  refine Set.mem_biUnion (x := la) ?_ ⟨hv, hla'⟩
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  refine (mem_extPrime la _).1 ?_ m
  by_contra hrs
  have hz : ∀ y : R, y ∉ extPrime (Fin D) la → v (algebraMap R Ω y) = 0 := fun y hy =>
    le_antisymm (not_lt.1 fun h => hy ((hla' y).2.1 h)) (hla' y).1
  have h1 := nonneg_of_isIntegral v (fun y => (hla' y).1) hr
  have h2 := nonneg_of_isIntegral v (fun y => (hla' y).1) hs
  rw [Algebra.smul_def, AddValuation.map_mul,
    hz _ (fun h => hrs (Ideal.mul_mem_right _ _ h)), zero_add] at h1
  rw [Algebra.smul_def, AddValuation.map_mul,
    hz _ (fun h => hrs (Ideal.mul_mem_left _ _ h)), zero_add] at h2
  refine hvg (ValPl.wt_add_eq_zero h1 h2 ?_)
  rw [← AddValuation.map_mul, mul_inv_cancel₀ hg, AddValuation.map_one]

end GlobalTheory
