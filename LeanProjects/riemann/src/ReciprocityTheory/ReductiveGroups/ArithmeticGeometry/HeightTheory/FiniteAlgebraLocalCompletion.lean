import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPrecompleteFiniteModule

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion

open IsLocalRing Polynomial

theorem isPrecomplete_finite_module {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  first | exact UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module .. | (apply UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> first | assumption | infer_instance)

theorem isAdicComplete_finite_algebra {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have := isPrecomplete_finite_module (maximalIdeal R) S
  exact ⟨⟩

theorem map_maximalIdeal_le_maximal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) (hn : n.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ n := by
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem finite_maximal_ideals_of_finite {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] : {n : Ideal S | n.IsMaximal}.Finite := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (S ⧸ J)).image
    (Ideal.comap (Ideal.Quotient.mk J))).subset ?_
  intro n hn
  refine ⟨n.map (Ideal.Quotient.mk J), ?_, ?_⟩
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    have : n.IsMaximal := hn
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hJ)
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hJ

theorem exists_pow_mem_map_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (b : S) (hb : ∀ n : Ideal S, n.IsMaximal → b ∈ n) :
    ∃ N : ℕ, 0 < N ∧ b ^ N ∈ (maximalIdeal R).map (algebraMap R S) := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
  have hmem : Ideal.Quotient.mk J b ∈ (⊥ : Ideal (S ⧸ J)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro q ⟨-, hq⟩
    have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := q)
    exact hb _ this
  have h1 : Ideal.Quotient.mk J (b ^ (k + 1)) = 0 := by
    have := Ideal.pow_mem_pow hmem k
    rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    rw [pow_succ, map_mul, map_pow, this, zero_mul]
  exact ⟨k + 1, k.succ_pos, Ideal.Quotient.eq_zero_iff_mem.mp h1⟩

theorem exists_idempotent_henselian {S : Type*} [CommRing S] (J : Ideal S) [HenselianRing S J] (x : S) (N : ℕ)
    (hN : (x * x - x) ^ (N + 1) ∈ J) : ∃ e s : S, e * e = e ∧ e - x = s * (x * x - x) := by
  have hnil : (Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2) ^ (N + 1) = 0 := by
    have : Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2 = -(Ideal.Quotient.mk J (x * x - x)) := by
      simp only [map_sub, map_mul, pow_two, neg_sub]
    rw [this, neg_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hN, mul_zero]
  have hid := isIdempotentElem_one_sub_one_sub_pow_pow _ (N + 1) hnil
  have hq : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      1 - (1 - Ideal.Quotient.mk J x ^ (N + 1)) ^ (N + 1) := by simp
  have hid' : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) *
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) := by rw [hq]; exact hid.eq
  have hxW : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {x * x - x}) x) := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hqW : Ideal.Quotient.mk (Ideal.span {x * x - x}) (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk (Ideal.span {x * x - x}) x := by
    simp only [map_sub, map_one, map_pow, hxW.pow_succ_eq, hxW.one_sub.pow_succ_eq, sub_sub_cancel]
  generalize 1 - (1 - x ^ (N + 1)) ^ (N + 1) = e0 at hid' hqW
  have h3 : e0 - x ∈ Ideal.span {x * x - x} := Ideal.Quotient.eq.1 hqW
  have h4 : e0 * e0 - e0 ∈ Ideal.span {x * x - x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hqW, hxW.eq, sub_self]
  have h1 : (X ^ 2 - X : S[X]).eval e0 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [eval_sub, eval_pow, eval_X, map_sub, map_pow, pow_two, hid', sub_self]
  have hd : (X ^ 2 - X : S[X]).derivative.eval e0 = 2 * e0 - 1 := by
    simp; ring
  have h2 : IsUnit (Ideal.Quotient.mk J ((X ^ 2 - X : S[X]).derivative.eval e0)) := by
    rw [hd]
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk J (2 * e0 - 1), ?_⟩
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hid'
  have hmon : (X ^ 2 - X : S[X]).Monic :=
    monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  obtain ⟨e, he, hee⟩ := HenselianRing.is_henselian _ hmon e0 h1 h2
  have hee' : e * e = e := by
    have := he.eq_zero
    simp only [eval_sub, eval_pow, eval_X] at this
    linear_combination this
  have hu2 : (2 * e - 1) * (2 * e - 1) = 1 := by linear_combination 4 * hee'
  have hdu : IsUnit (e - e0 - (2 * e - 1)) := by
    have : e - e0 - (2 * e - 1) = (-(2 * e - 1)) * ((e - e0) * (-(2 * e - 1)) + 1) := by
      linear_combination (-(e - e0)) * hu2
    rw [this]
    exact (isUnit_iff_exists_inv.2 ⟨-(2 * e - 1), by linear_combination hu2⟩).mul
      (Ideal.mem_jacobson_bot.1 (HenselianRing.jac hee) _)
  have hdW : e - e0 ∈ Ideal.span {x * x - x} := by
    obtain ⟨v, hv⟩ := hdu.exists_left_inv
    have hdd : (e - e0) * (e - e0 - (2 * e - 1)) = e0 * e0 - e0 := by
      linear_combination (-1 : S) * hee'
    have : e - e0 = v * (e0 * e0 - e0) := by
      linear_combination (-(e - e0)) * hv + v * hdd
    rw [this]; exact Ideal.mul_mem_left _ _ h4
  have h5 : e - x ∈ Ideal.span {x * x - x} := by
    have : e - x = (e - e0) + (e0 - x) := by ring
    rw [this]; exact Ideal.add_mem _ hdW h3
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h5
  exact ⟨e, s, hee', hs.symm⟩

theorem isLocalRing_finite_domain {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hloc
  obtain ⟨M1, hM1⟩ := Ideal.exists_maximal S
  have hex : ∃ M2 : Ideal S, M2.IsMaximal ∧ M2 ≠ M1 := by
    by_contra h
    push Not at h
    exact hloc (IsLocalRing.of_unique_max_ideal ⟨M1, hM1, fun M hM => h M hM⟩)
  obtain ⟨M2, hM2, h12⟩ := hex
  set F := (finite_maximal_ideals_of_finite (R := R) S).toFinset.filter (· ≠ M1) with hF
  have hmemF : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → N ∈ F := by
    intro N hN hN1
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hN, hN1⟩
  have hcop : M1 ⊔ F.inf id = ⊤ := by
    by_contra hne
    have hle : F.inf id ≤ M1 := by
      rw [hM1.eq_of_le hne le_sup_left]; exact le_sup_right
    obtain ⟨N, hN, hNle⟩ := (hM1.isPrime.inf_le').1 hle
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at hN
    exact hN.2 ((hN.1 : N.IsMaximal).eq_of_le hM1.ne_top hNle)
  have h1 : (1 : S) ∈ M1 ⊔ F.inf id := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have hx1 : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → x - 1 ∈ N := by
    intro N hN hN1
    have : y ∈ N := Finset.inf_le (f := id) (hmemF N hN hN1) hy
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]; exact N.neg_mem (by assumption)
  have hall : ∀ N : Ideal S, N.IsMaximal → x * x - x ∈ N := by
    intro N hN
    by_cases hN1 : N = M1
    · subst hN1; exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx) hx
    · have := hx1 N hN hN1
      have e : x * x - x = x * (x - 1) := by ring
      rw [e]; exact Ideal.mul_mem_left _ _ this
  obtain ⟨k, hk, hkJ⟩ := exists_pow_mem_map_maximalIdeal (R := R) S _ hall
  have : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := isAdicComplete_finite_algebra S
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨e, s, hee, hes⟩ := exists_idempotent_henselian ((maximalIdeal R).map (algebraMap R S)) x k' hkJ
  have hxx1 : x * x - x ∈ M1 := hall M1 hM1
  have hxx2 : x * x - x ∈ M2 := hall M2 hM2
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hee) with h0 | h0
  · apply hM2.ne_top
    rw [Ideal.eq_top_iff_one]
    have ha : -x ∈ M2 := by
      have : -x = s * (x * x - x) := by rw [← hes, h0]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hxx2
    have hb := hx1 M2 hM2 h12
    have : (1 : S) = -(x - 1) + -(-x) := by ring
    rw [this]; exact M2.add_mem (M2.neg_mem hb) (M2.neg_mem ha)
  · apply hM1.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : S) = s * (x * x - x) + x := by rw [← hes, h0]; ring
    rw [this]; exact M1.add_mem (Ideal.mul_mem_left _ _ hxx1) hx

section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (L : Type*) [Field L] [Algebra R L] [FaithfulSMul R L] [Module.Finite R (integralClosure R L)]

theorem cl_inj : Function.Injective (algebraMap R (integralClosure R L)) := by
  intro x y h
  apply FaithfulSMul.algebraMap_injective R L
  exact congrArg Subtype.val h

theorem cl_isLocalRing [IsAdicComplete (maximalIdeal R) R] : IsLocalRing (integralClosure R L) :=
  isLocalRing_finite_domain (R := R) (integralClosure R L)

theorem cl_isLocalHom : IsLocalHom (algebraMap R (integralClosure R L)) :=
  RingHom.IsIntegral.isLocalHom (fun x => (Algebra.IsIntegral.isIntegral x : IsIntegral R x))
    (cl_inj R L)

end

section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]

include K

theorem cl_faithful : FaithfulSMul R L :=
  (faithfulSMul_iff_algebraMap_injective R L).2 (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))

variable [Module.Finite R (integralClosure R L)]

theorem cl_dvr [IsAdicComplete (maximalIdeal R) R] :
    IsDiscreteValuationRing (integralClosure R L) := by
  have := cl_faithful R K L
  have : IsLocalRing (integralClosure R L) := cl_isLocalRing R L
  have : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.IsIntegral R (integralClosure R L) := IsIntegralClosure.isIntegral_algebra R L
  have : IsNoetherianRing (integralClosure R L) :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower R inferInstance)
  have hD : IsDedekindDomain (integralClosure R L) :=
    { ‹IsNoetherianRing (integralClosure R L)›,
      Ring.DimensionLEOne.of_isIntegral R (integralClosure R L),
      (isIntegrallyClosed_iff L).mpr fun {x} hx =>
        ⟨IsIntegralClosure.mk' (integralClosure R L) x (isIntegral_trans (R := R) _ hx),
          IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain (integralClosure R L) }
  have hnf : ¬ IsField (integralClosure R L) := fun h =>
    (isField_iff_maximalIdeal_eq.not.mpr IsDiscreteValuationRing.not_a_field')
      (isField_of_isIntegral_of_isField (cl_inj R L) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 0 2).mpr hD

end

end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
