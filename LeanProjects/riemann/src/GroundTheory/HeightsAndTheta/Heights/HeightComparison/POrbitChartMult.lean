import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMultLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing

noncomputable section

namespace OrbitChartMult

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem prod_X_pow_eq_monomial_fintype {D : Type*} [CommRing D] (d : ι → ℕ) :
    ∏ k, (X k : MvPolynomial ι D) ^ d k = monomial (Finsupp.equivFunOnFinite.symm d) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp

omit [DecidableEq ι] in

theorem coeff_sum_C_mul_prod_X_pow {D : Type*} [CommRing D] (S : Finset (ι → ℕ))
    (a : (ι → ℕ) → D) {d : ι → ℕ} (hd : d ∈ S) :
    coeff (Finsupp.equivFunOnFinite.symm d) (∑ e ∈ S, C (a e) * ∏ k, (X k : MvPolynomial ι D) ^ e k) =
      a d := by
  classical
  simp only [prod_X_pow_eq_monomial_fintype, coeff_sum, coeff_C_mul, coeff_monomial,
    EmbeddingLike.apply_eq_iff_eq, mul_ite, mul_one, mul_zero]
  simp [hd]

section General

variable {O : Type*} [CommRing O] [IsDomain O]

omit [IsDomain O] in

abbrev fibO (ι : Type) (m : Ideal O) : Ideal (MvPolynomial ι O) := Ideal.map C m

omit [IsDomain O] in
instance fibO_isPrime (ι : Type) (m : Ideal O) [m.IsPrime] : (fibO ι m).IsPrime := by
  have h : fibO ι m = RingHom.ker (map (Ideal.Quotient.mk m) :
      MvPolynomial ι O →+* MvPolynomial ι (O ⧸ m)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [h]
  exact RingHom.ker_isPrime _

omit [IsDomain O] in

abbrev locB (ι : Type) (m : Ideal O) [m.IsPrime] := Localization.AtPrime (fibO ι m)

theorem locB_injective (ι : Type) (m : Ideal O) [m.IsPrime] :
    Function.Injective (algebraMap (MvPolynomial ι O) (locB ι m)) :=
  IsLocalization.injective (locB ι m) (Ideal.primeCompl_le_nonZeroDivisors (fibO ι m))

omit [IsDomain O] in

theorem isUnit_prod_X_pow (m : Ideal O) [hm : m.IsPrime] (a : ι → ℕ) :
    IsUnit (algebraMap (MvPolynomial ι O) (locB ι m) (∏ k, X k ^ a k)) := by
  have hnot : (∏ k, X k ^ a k : MvPolynomial ι O) ∉ fibO ι m := by
    intro h
    have h' := MvPolynomial.mem_map_C_iff.mp h (Finsupp.equivFunOnFinite.symm a)
    rw [prod_X_pow_eq_monomial_fintype, coeff_monomial, if_pos rfl] at h'
    exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h')
  exact IsLocalization.map_units (locB ι m) (⟨∏ k, X k ^ a k, hnot⟩ : (fibO ι m).primeCompl)

omit [Fintype ι] [DecidableEq ι] [IsDomain O] in

theorem isUnit_C_locB (m : Ideal O) [m.IsPrime] (u : m.primeCompl) :
    IsUnit (((algebraMap (MvPolynomial ι O) (locB ι m)).comp C) (u : O)) := by
  classical
  have hnot : (C (u : O) : MvPolynomial ι O) ∉ fibO ι m := fun h ↦ u.2 (by
    have h' := MvPolynomial.mem_map_C_iff.mp h 0
    rwa [coeff_C, if_pos rfl] at h')
  exact IsLocalization.map_units (locB ι m) (⟨C (u : O), hnot⟩ : (fibO ι m).primeCompl)

omit [IsDomain O] in

abbrev betaB (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O) (m : Ideal O) [m.IsPrime] :
    MvPolynomial (Coord n) ℤ →+* locB ι m :=
  (algebraMap (MvPolynomial ι O) (locB ι m)).comp γ

variable {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]

include hγ in
omit [IsDomain O] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] in
theorem betaB_X (p : Coord n) :
    betaB γ (V.map ε) (X p) = algebraMap (MvPolynomial ι O) (locB ι (V.map ε))
      (C (ε (X p)) * X p.1) := by
  rw [betaB, RingHom.comp_apply, hγ (isWeightedHomogeneous_X ℤ (coordDeg n) p)]
  congr 2
  simp [coordDeg, Pi.single_apply, pow_ite]

omit [Fintype ι] [DecidableEq ι] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] in

theorem betaB_eq_zero_iff (F : MvPolynomial (Coord n) ℤ) :
    betaB γ (V.map ε) F = 0 ↔ γ F = 0 := by
  rw [betaB, RingHom.comp_apply, map_eq_zero_iff _ (locB_injective ι _)]

include hγ in
omit [IsDomain O] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] in

theorem betaB_mem_maximalIdeal_iff
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hD : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
      ε F ∈ V.map ε → F ∈ V) (F : MvPolynomial (Coord n) ℤ) :
    betaB γ (V.map ε) F ∈ maximalIdeal (locB ι (V.map ε)) ↔ F ∈ V := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := coordDeg n) F
  have hsum : F = ∑ e ∈ hfin.toFinset, weightedHomogeneousComponent (coordDeg n) e F := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) F, finsum_eq_sum _ hfin]
  have hcone : γ F = ∑ e ∈ hfin.toFinset,
      C (ε (weightedHomogeneousComponent (coordDeg n) e F)) * ∏ k, X k ^ e k := by
    conv_lhs => rw [hsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun e _ ↦ hγ (weightedHomogeneousComponent_isWeightedHomogeneous e F)
  rw [betaB, RingHom.comp_apply,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (locB ι (V.map ε)) (fibO ι (V.map ε)), hcone]
  constructor
  · intro h
    rw [hsum]
    refine V.sum_mem fun e he ↦ ?_
    have h' := MvPolynomial.mem_map_C_iff.mp h (Finsupp.equivFunOnFinite.symm e)
    rw [coeff_sum_C_mul_prod_X_pow _ _ he] at h'
    exact hD (weightedHomogeneousComponent_isWeightedHomogeneous e F) h'
  · intro h
    exact Ideal.sum_mem _ fun e _ ↦ Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hV F h e)))

include hγ in
omit [IsDomain O] in

theorem exists_betaB_mul_eq [hVp : V.IsPrime] (hε : Function.Surjective ε)
    (c : (k : ι) → Fin (n k + 1)) (hXc : ∀ k, ε (X ⟨k, c k⟩) = 1)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hmax : ∀ F, betaB γ (V.map ε) F ∈ maximalIdeal (locB ι (V.map ε)) ↔ F ∈ V)
    (b : locB ι (V.map ε)) :
    ∃ F t, t ∉ V ∧ betaB γ (V.map ε) t * b = betaB γ (V.map ε) F := by
  have h1 : (1 : MvPolynomial (Coord n) ℤ) ∉ V := (Ideal.ne_top_iff_one V).mp hVp.ne_top
  let S : Subring (locB ι (V.map ε)) :=
    { carrier := {b | ∃ F t, t ∉ V ∧ betaB γ (V.map ε) t * b = betaB γ (V.map ε) F}
      mul_mem' := by
        rintro _ _ ⟨F₁, t₁, h₁, e₁⟩ ⟨F₂, t₂, h₂, e₂⟩
        refine ⟨F₁ * F₂, t₁ * t₂, fun h ↦ (hVp.mem_or_mem h).elim h₁ h₂, ?_⟩
        rw [map_mul, map_mul, ← e₁, ← e₂]
        ring
      one_mem' := ⟨1, 1, h1, by simp⟩
      add_mem' := by
        rintro _ _ ⟨F₁, t₁, h₁, e₁⟩ ⟨F₂, t₂, h₂, e₂⟩
        refine ⟨F₁ * t₂ + F₂ * t₁, t₁ * t₂, fun h ↦ (hVp.mem_or_mem h).elim h₁ h₂, ?_⟩
        rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
        ring
      zero_mem' := ⟨0, 1, h1, by simp⟩
      neg_mem' := by
        rintro _ ⟨F, t, h, e⟩
        exact ⟨-F, t, h, by rw [map_neg, ← e]; ring⟩ }
  have hβ : ∀ F, betaB γ (V.map ε) F ∈ S := fun F ↦ ⟨F, 1, h1, by simp⟩
  have hinv : ∀ (b : locB ι (V.map ε)) (hb : IsUnit b), b ∈ S →
      (↑hb.unit⁻¹ : locB ι (V.map ε)) ∈ S := by
    rintro b hb ⟨F, t, ht, e⟩
    have htu : IsUnit (betaB γ (V.map ε) t) := by
      by_contra h
      exact ht ((hmax t).mp ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)))
    have hF : F ∉ V := fun hF ↦ mem_nonunits_iff.mp ((mem_maximalIdeal _).mp ((hmax F).mpr hF))
      (e ▸ htu.mul hb)
    refine ⟨t, F, hF, ?_⟩
    rw [← e, mul_assoc, IsUnit.mul_val_inv, mul_one]
  let ρ : O →+* locB ι (V.map ε) := (algebraMap (MvPolynomial ι O) (locB ι (V.map ε))).comp C
  have hρX : ∀ p : Coord n, betaB γ (V.map ε) (X ⟨p.1, c p.1⟩) * ρ (ε (X p)) =
      betaB γ (V.map ε) (X p) := fun p ↦ by
    rw [betaB_X ε γ hγ V, betaB_X ε γ hγ V, hXc]
    simp only [ρ, RingHom.comp_apply, map_one, one_mul]
    rw [← map_mul, mul_comm (X p.1)]
  have hρ : ∀ F, ρ (ε F) ∈ S := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C z =>
      rw [eq_intCast C z, map_intCast, map_intCast]
      exact intCast_mem S z
    | add p q hp hq =>
      rw [map_add, map_add]
      exact S.add_mem hp hq
    | mul_X p q hp =>
      rw [map_mul, map_mul]
      exact S.mul_mem hp ⟨X q, X ⟨q.1, c q.1⟩, hXV q.1, hρX q⟩
  have hP : ∀ p : MvPolynomial ι O, algebraMap _ (locB ι (V.map ε)) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C o =>
      obtain ⟨F, rfl⟩ := hε o
      exact hρ F
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | mul_X p k hp =>
      rw [map_mul]
      refine S.mul_mem hp ?_
      have e : algebraMap (MvPolynomial ι O) (locB ι (V.map ε)) (X k) =
          betaB γ (V.map ε) (X ⟨k, c k⟩) := by
        rw [betaB_X ε γ hγ V, hXc]
        simp
      rw [e]
      exact hβ _
  obtain ⟨p, q, rfl⟩ := IsLocalization.exists_mk'_eq (fibO ι (V.map ε)).primeCompl b
  have hq : IsUnit (algebraMap _ (locB ι (V.map ε)) (q : MvPolynomial ι O)) :=
    IsLocalization.map_units _ q
  have e : IsLocalization.mk' (locB ι (V.map ε)) p q = algebraMap _ _ p * ↑hq.unit⁻¹ := by
    rw [← IsLocalization.mk'_spec (locB ι (V.map ε)) p q, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hmem : IsLocalization.mk' (locB ι (V.map ε)) p q ∈ S := by
    rw [e]
    exact S.mul_mem (hP p) (hinv _ hq (hP q))
  exact hmem

end General

section Abstract

variable {R B : Type*} [CommRing R] [CommRing B]

theorem length_localizedModule_quot_eq (β : R →+* B) (V W : Ideal R) [hVp : V.IsPrime] (s : R)
    (hker : ∀ F, β F = 0 ↔ F ∈ W) (hunit : ∀ t : V.primeCompl, IsUnit (β t))
    (hgood : ∀ b, ∃ F t, t ∉ V ∧ β t * b = β F) :
    Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (R ⧸ (W ⊔ Ideal.span {s}))) =
      Module.length B (B ⧸ Ideal.span {β s}) := by
  classical
  let algV : Algebra (Localization.AtPrime V) B :=
    (IsLocalization.lift (M := V.primeCompl) (S := Localization.AtPrime V) hunit).toAlgebra
  let algR : Algebra R B := β.toAlgebra
  have : IsScalarTower R (Localization.AtPrime V) B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hunit).symm
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime V) B) := by
    intro b
    obtain ⟨F, t, ht, e⟩ := hgood b
    refine ⟨IsLocalization.mk' _ F (⟨t, ht⟩ : V.primeCompl), ?_⟩
    show IsLocalization.lift hunit (IsLocalization.mk' _ F (⟨t, ht⟩ : V.primeCompl)) = b
    rw [IsLocalization.lift_mk'_spec]
    exact e.symm
  let I : Ideal B := Ideal.span {β s}
  let J : Ideal R := W ⊔ Ideal.span {s}
  let f : R →ₗ[R] B ⧸ I := ((Ideal.Quotient.mkₐ R I).comp (Algebra.ofId R B)).toLinearMap
  have hf : ∀ F, f F = Ideal.Quotient.mk I (β F) := fun F ↦ rfl
  have hJ : J ≤ LinearMap.ker f := by
    refine sup_le (fun F hF ↦ ?_) (Ideal.span_le.mpr fun F hF ↦ ?_)
    · rw [LinearMap.mem_ker, hf, (hker F).mpr hF, map_zero]
    · rw [Set.mem_singleton_iff] at hF
      subst hF
      rw [SetLike.mem_coe, LinearMap.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
  let g : (R ⧸ J) →ₗ[R] B ⧸ I := Submodule.liftQ J f hJ
  have hg : ∀ F, g (Ideal.Quotient.mk J F) = Ideal.Quotient.mk I (β F) := fun F ↦ rfl
  have hsmul : ∀ (r : R) (y : B ⧸ I), r • y = β r • y := fun r y ↦ (algebraMap_smul _ r y).symm
  have hloc : IsLocalizedModule V.primeCompl g := by
    constructor
    · intro t
      rw [Module.End.isUnit_iff]
      obtain ⟨u, hu⟩ := hunit t
      have hsm : ∀ y : B ⧸ I, (algebraMap R (Module.End R (B ⧸ I)) t) y = (u : B) • y := fun y ↦ by
        rw [Module.algebraMap_end_apply, hsmul, hu]
      constructor
      · intro y z h
        rw [hsm, hsm] at h
        have := congrArg (fun w ↦ (↑u⁻¹ : B) • w) h
        simpa [smul_smul] using this
      · intro y
        refine ⟨(↑u⁻¹ : B) • y, ?_⟩
        rw [hsm, smul_smul, Units.mul_inv, one_smul]
    · intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨F, t, ht, e⟩ := hgood b
      refine ⟨(Ideal.Quotient.mk J F, ⟨t, ht⟩), ?_⟩
      show (t : R) • Ideal.Quotient.mk I b = g (Ideal.Quotient.mk J F)
      rw [hsmul, hg, ← e]
      rfl
    · intro y₁ y₂ h
      obtain ⟨F₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨F₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      rw [hg, hg, Ideal.Quotient.eq, ← map_sub] at h
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h
      obtain ⟨G, t, ht, e⟩ := hgood b
      refine ⟨⟨t, ht⟩, ?_⟩
      have hmem : t * (F₁ - F₂) - G * s ∈ W := by
        rw [← hker, map_sub, map_mul, map_mul, ← hb, ← e]
        ring
      show Ideal.Quotient.mk J (t * F₁) = Ideal.Quotient.mk J (t * F₂)
      rw [Ideal.Quotient.eq]
      have e2 : t * F₁ - t * F₂ = (t * (F₁ - F₂) - G * s) + G * s := by ring
      rw [e2]
      exact J.add_mem (Ideal.mem_sup_left hmem)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  let eV := (IsLocalizedModule.iso V.primeCompl g).extendScalarsOfIsLocalization V.primeCompl
    (Localization.AtPrime V)
  rw [eV.length_eq, Module.length_eq_of_surjective hsurj]

theorem length_quot_map_eq {A : Type*} [CommRing A] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal _))
    exact Module.length_eq_one _ _
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, h, h1, mul_one]

end Abstract

section General2

variable {O : Type*} [CommRing O] [IsDomain O]
  {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]

include hγ in

theorem multAt_eq_localQuotLength_of [hVp : V.IsPrime] (hε : Function.Surjective ε)
    (W : Ideal (MvPolynomial (Coord n) ℤ)) (hW : ∀ F, γ F = 0 ↔ F ∈ W)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hD : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
      ε F ∈ V.map ε → F ∈ V)
    (c : (k : ι) → Fin (n k + 1)) (hXc : ∀ k, ε (X ⟨k, c k⟩) = 1)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) {s : MvPolynomial (Coord n) ℤ}
    {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a) :
    Geo.multAt (W ⊔ Ideal.span {s}) V = localQuotLength (V.map ε) (ε s) := by
  classical
  have hmax := betaB_mem_maximalIdeal_iff ε γ hγ V hV hD
  have hgood := exists_betaB_mul_eq ε γ hγ V hε c hXc hXV hmax
  have hker : ∀ F, betaB γ (V.map ε) F = 0 ↔ F ∈ W := fun F ↦
    (betaB_eq_zero_iff ε γ V F).trans (hW F)
  have hunit : ∀ t : V.primeCompl, IsUnit (betaB γ (V.map ε) t) := fun t ↦ by
    by_contra h
    exact t.2 ((hmax t).mp ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)))
  let algAB : Algebra (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) :=
    (IsLocalization.lift (M := (V.map ε).primeCompl) (S := Localization.AtPrime (V.map ε))
      (isUnit_C_locB (ι := ι) (V.map ε))).toAlgebra
  have : IsScalarTower O (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq O (MvPolynomial ι O) (locB ι (V.map ε)), algebraMap_eq]
      exact (IsLocalization.lift_comp (isUnit_C_locB (ι := ι) (V.map ε))).symm)
  have : Module.Flat (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (V.map ε)) (V.map ε).primeCompl
      (locB ι (V.map ε))).mpr inferInstance
  have hmaxA : (maximalIdeal (Localization.AtPrime (V.map ε))).map
      (algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε))) =
      maximalIdeal (locB ι (V.map ε)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq O (MvPolynomial ι O),
      ← Ideal.map_map, algebraMap_eq]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have : IsLocalHom (algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε))) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have h2 : algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) a ∈
        maximalIdeal (locB ι (V.map ε)) := by
      rw [← hmaxA]
      exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna))
    exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h2) ha
  have hI : Ideal.span {betaB γ (V.map ε) s} =
      (Ideal.span {algebraMap O (Localization.AtPrime (V.map ε)) (ε s)}).map
        (algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε))) := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply O (MvPolynomial ι O) (locB ι (V.map ε)), algebraMap_eq,
      betaB, RingHom.comp_apply, hγ hs, map_mul,
      Ideal.span_singleton_mul_right_unit (isUnit_prod_X_pow _ a)]
  rw [Geo.multAt, dif_pos hVp,
    length_localizedModule_quot_eq (betaB γ (V.map ε)) V W s hker hunit hgood, hI,
    length_quot_map_eq hmaxA]
  rfl

end General2

end OrbitChartMult

theorem OrbitChartMult.proof : OrbitChartMult.Statement := by
  intro ι _ _ _ n A x s _hx hs V hV c hXV hm
  classical
  have hVmin : V ∈ (orbitIdeal x ⊔ Ideal.span {s}).minimalPrimes := hV.1
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  obtain ⟨a, -, hsa, -⟩ := hs
  have hVh : Geo.IsMultiHomogIdeal (ι := blockIdx n) V :=
    Geo.isMultiHomogIdeal_of_mem_minimalPrimes (OrbitCurve.isMultiHomogIdeal_orbitIdeal x) hsa hVmin
  have hc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hXV k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  have hcomp : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V :=
    fun v hv e ↦ weightedHomogeneousComponent_mem_of_isMultiHomogIdeal hVh hv e
  have : (Ideal.map (chartEval x c) V).IsPrime := hm
  exact multAt_eq_localQuotLength_of (chartEval x c) (chartCone x c (chartRing x c))
    (fun hF ↦ by rw [chartCone_of_isWeightedHomogeneous x c _ hF, Algebra.algebraMap_self_apply])
    V (chartEval_surjective x c) (orbitIdeal x) (chartCone_eq_zero_iff x c hc) hcomp
    (fun hF hm' ↦ mem_of_chartEval_mem_chartPoint x c hc hWV hcomp hXV hF hm') c
    (chartEval_X_chart x c hc) hXV ((geoMultiHomog_iff s a).mp hsa)

end

end GroundTheory.Heights₂.Heights
