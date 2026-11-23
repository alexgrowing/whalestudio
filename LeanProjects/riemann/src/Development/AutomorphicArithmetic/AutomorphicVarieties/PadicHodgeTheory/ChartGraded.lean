import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

private theorem cg_max {E σ : Type} [Field E] : maximalIdeal (MvPowerSeries σ E) = GlobalTheory.germIdeal σ E := by
  ext g
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  simp [GlobalTheory.germIdeal, RingHom.mem_ker]

private theorem cg_ext {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    [IsFractionRing O E] {n : ℕ} {I : Ideal R} {x : R →ₐ[O] O} {φ : R →ₐ[O] MvPowerSeries (Fin n) E}
    (hφ : UpperTheory.V.Loc.IsCompl I x φ) {z : Fin n → R} (hz : ∀ i, φ (z i) = MvPowerSeries.X i)
    (α β : R →ₐ[O] MvPowerSeries (Fin n) E)
    (hα : ∀ a, MvPowerSeries.constantCoeff (α a) = algebraMap O E (x a))
    (hβ : ∀ a, MvPowerSeries.constantCoeff (β a) = algebraMap O E (x a))
    (hI : ∀ a ∈ I, α a = β a) (hzz : ∀ i, α (z i) = β (z i)) (a : R) : α a = β a := by
  classical
  have hm := cg_max (E := E) (σ := Fin n)
  have hA : ∀ (γ : R →ₐ[O] MvPowerSeries (Fin n) E),
      (∀ a, MvPowerSeries.constantCoeff (γ a) = algebraMap O E (x a)) →
      ∀ N, ∀ b ∈ RingHom.ker x ^ N, γ b ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro γ hγ N b hb
    have h1 : Ideal.map γ (RingHom.ker x) ≤ GlobalTheory.germIdeal (Fin n) E := by
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [hγ, RingHom.mem_ker.mp hc, map_zero]
    have h2 : Ideal.map γ (RingHom.ker x ^ N) ≤ GlobalTheory.germIdeal (Fin n) E ^ N := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' h1 N
    exact h2 (Ideal.mem_map_of_mem γ hb)
  have hB : ∀ N, ∀ b ∈ RingHom.ker x ^ N ⊔ I, α b - β b ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro N b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
    have hv0 : α v - β v = 0 := sub_eq_zero.mpr (hI v hv)
    rw [map_add, map_add, add_sub_add_comm, hv0, add_zero]
    exact Ideal.sub_mem _ (hA α hα N u hu) (hA β hβ N u hu)
  have hC : ∀ p : MvPolynomial (Fin n) O, α (MvPolynomial.aeval z p) = β (MvPolynomial.aeval z p) := by
    intro p
    have hcomp : α.comp (MvPolynomial.aeval z) = β.comp (MvPolynomial.aeval z) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [hzz i]
    exact AlgHom.congr_fun hcomp p
  have hP : ∀ p : MvPolynomial (Fin n) O, φ (MvPolynomial.aeval z p) =
      ((MvPolynomial.map (algebraMap O E) p : MvPolynomial (Fin n) E) : MvPowerSeries (Fin n) E) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.aeval_C, AlgHom.commutes, MvPolynomial.map_C, MvPolynomial.coe_C,
        MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp only [map_add, hp, hq, MvPolynomial.coe_add]
    | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, hz i, MvPolynomial.map_X, MvPolynomial.coe_mul,
        MvPolynomial.coe_X]
  have hmain : ∀ N, ∃ e : O, e ≠ 0 ∧ e • (α a - β a) ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro N
    set s := (Finsupp.finite_of_degree_lt (σ := Fin n) N).toFinset with hs
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
      (fun d => MvPowerSeries.coeff d (φ a))
    have hb' : ∀ d ∈ s, ∃ k : O, algebraMap O E k = (b : O) • MvPowerSeries.coeff d (φ a) :=
      fun d hd => RingHom.mem_rangeS.mp (hb d hd)
    choose! k hk using hb'
    set p : MvPolynomial (Fin n) O := ∑ d ∈ s, MvPolynomial.monomial d (k d) with hp
    set y : R := (b : O) • a - MvPolynomial.aeval z p with hy
    have hφy : φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N := by
      rw [hm, GlobalTheory.mem_germIdeal_pow_iff]
      intro d hd
      have hds : d ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        exact hd
      have hcp : MvPolynomial.coeff d p = k d := by
        rw [hp, MvPolynomial.coeff_sum]
        simp only [MvPolynomial.coeff_monomial]
        rw [Finset.sum_ite_eq' s d (fun e => k e), if_pos hds]
      rw [hy, map_sub, map_smul, hP, map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_map, hcp,
        hk d hds]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc0, hc⟩ := hφ.inj N y hφy
    refine ⟨c * b, mul_ne_zero hc0 (nonZeroDivisors.ne_zero b.2), ?_⟩
    have heq : α (c • y) - β (c • y) = (c * (b : O)) • (α a - β a) := by
      rw [hy]
      simp only [map_smul, map_sub]
      rw [hC p, ← smul_sub, sub_sub_sub_cancel_right, ← smul_sub, mul_smul]
    rw [← heq]
    exact hB N _ hc
  rw [← sub_eq_zero]
  ext d
  obtain ⟨e, he0, he⟩ := hmain (d.degree + 1)
  rw [GlobalTheory.mem_germIdeal_pow_iff] at he
  have h1 := he d (Nat.lt_succ_self _)
  change e • MvPowerSeries.coeff d (α a - β a) = 0 at h1
  rw [Algebra.smul_def, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).mpr he0)
  · rw [map_zero]
    exact h1

theorem UpperTheory.V.Loc.chartGraded :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (z : Fin n → R) (w : Fin n → ℤ) (θ : R →ₐ[O] R) (t : Oˣ), UpperTheory.V.Loc.IsCompl I x φ → (∀ i, φ (z i) = MvPowerSeries.X i) → x.comp θ = x → (∀ a ∈ I, θ a ∈ I) → (Function.Injective fun j : ℤ => t ^ j) → (∀ i, θ (z i) = algebraMap O R ((t ^ w i : Oˣ) : O) * z i) → ∀ (j : ℤ) (a : R), θ a = algebraMap O R ((t ^ j : Oˣ) : O) * a → φ a ∈ wtPart E w j := by
  intro O R E _ _ _ _ _ _ _ n I x φ z w θ t hφ hz hxθ hθI hinj hθz j a ha
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin n → E, c = fun i => algebraMap O E ((t ^ w i : Oˣ) : O) := ⟨_, rfl⟩
  have hρC : ∀ e : E, MvPowerSeries.rescale c (MvPowerSeries.C e) = MvPowerSeries.C e := by
    intro e
    ext m
    rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
    split_ifs with hm
    · subst hm
      simp
    · simp
  let β : R →ₐ[O] MvPowerSeries (Fin n) E :=
    AlgHom.mk ((MvPowerSeries.rescale c).comp φ.toRingHom) (fun r => by
      show MvPowerSeries.rescale c (φ (algebraMap O R r)) = _
      rw [AlgHom.commutes, MvPowerSeries.algebraMap_apply, hρC])
  have hβ_apply : ∀ r, β r = MvPowerSeries.rescale c (φ r) := fun r => rfl
  have hker : ∀ r ∈ I, φ r = 0 := by
    intro r hr
    rw [← RingHom.mem_ker, hφ.ker]
    exact hr
  have key := cg_ext hφ hz (φ.comp θ) β
    (by
      intro r
      rw [AlgHom.comp_apply, hφ.const, ← AlgHom.comp_apply, hxθ])
    (by
      intro r
      rw [hβ_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale,
        Finsupp.prod_zero_index, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const])
    (by
      intro r hr
      rw [AlgHom.comp_apply, hker _ (hθI r hr), hβ_apply, hker r hr, map_zero])
    (by
      intro i
      rw [AlgHom.comp_apply, hθz i, map_mul, AlgHom.commutes, hz i, hβ_apply, hz i,
        MvPowerSeries.algebraMap_apply]
      ext m
      rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      split_ifs with hm
      · subst hm
        simp [hc]
      · simp) a
  have hθa : φ (θ a) = MvPowerSeries.C (algebraMap O E ((t ^ j : Oˣ) : O)) * φ a := by
    rw [ha, map_mul, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
  have key' : MvPowerSeries.C (algebraMap O E ((t ^ j : Oˣ) : O)) * φ a = MvPowerSeries.rescale c (φ a) := by
    rw [← hθa]
    exact key
  have hprod : ∀ m : Fin n →₀ ℕ,
      (m.prod fun i k => c i ^ k) = algebraMap O E ((t ^ (Finsupp.weight w m) : Oˣ) : O) := by
    intro m
    rw [hc, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    simp only [← map_pow, ← map_prod, ← Units.val_pow_eq_pow_val, ← Units.coe_prod]
    congr 2
    have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → ℤ), t ^ (∑ i ∈ s, f i) = ∏ i ∈ s, t ^ f i := by
      intro s f
      refine Finset.induction_on s (by simp) ?_
      intro i s hi ih
      rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
    rw [hsum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← zpow_natCast, ← zpow_mul, nsmul_eq_mul, mul_comm]
  change ∀ (m : Fin n →₀ ℕ), (Finsupp.weight w) m ≠ j → MvPowerSeries.coeff m (φ a) = 0
  intro m hm
  have hcm := congrArg (MvPowerSeries.coeff m) key'
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_rescale, hprod m, ← sub_eq_zero, ← sub_mul,
    mul_eq_zero] at hcm
  rcases hcm with h | h
  · exfalso
    apply hm
    rw [sub_eq_zero] at h
    have h3 : t ^ j = t ^ (Finsupp.weight w m) := Units.ext (IsFractionRing.injective O E h)
    exact (hinj h3).symm
  · exact h
