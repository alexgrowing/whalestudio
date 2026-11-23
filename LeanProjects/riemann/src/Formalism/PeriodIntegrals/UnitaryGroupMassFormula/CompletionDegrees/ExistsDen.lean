import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem exists_den {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (v : HeightOneSpectrum (𝓞 E))
    (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal))
    (e : E) (he : ‖φ e‖ ≤ 1) :
    ∃ s a : 𝓞 E, s ∉ v.asIdeal ∧ e * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
  classical
  have hunit : ∀ s : 𝓞 E, s ∉ v.asIdeal → ‖φ (algebraMap (𝓞 E) E s)‖ = 1 :=
    fun s hs => le_antisymm (hφ s).1 (not_lt.mp fun h => hs ((hφ s).2.mp h))
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hrel : ∀ u w : 𝓞 E, a * u = d * w →
      algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E d * algebraMap (𝓞 E) E u = algebraMap (𝓞 E) E w := by
    intro u w huw
    rw [div_mul_eq_mul_div, div_eq_iff hd0, ← map_mul, ← map_mul, huw, mul_comm]
  haveI : IsDomain (Localization.AtPrime v.asIdeal) := by
    first
      | infer_instance
      | exact IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors v.asIdeal)
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := by
    first
      | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) v.ne_bot _
      | infer_instance
  haveI : ValuationRing (Localization.AtPrime v.asIdeal) := inferInstance
  have hinj := IsLocalization.injective (Localization.AtPrime v.asIdeal)
    (Ideal.primeCompl_le_nonZeroDivisors v.asIdeal)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) d)
    (algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) a)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl c
  have hs : (s : 𝓞 E) ∉ v.asIdeal := s.2
  rcases hc with h | h
  · have key : algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (d * r) =
        algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (a * s) := by
      rw [map_mul, map_mul, ← h, ← IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r s]
      ring
    have hdr := hinj key
    exact ⟨s, r, hs, hrel s r hdr.symm⟩
  · have key : algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (a * r) =
        algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (d * s) := by
      rw [map_mul, map_mul, ← h, ← IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r s]
      ring
    have hdr := hinj key
    by_cases hr : r ∈ v.asIdeal
    · exfalso
      have hmul := hrel r s hdr
      have hn := congrArg (fun z => ‖φ z‖) hmul
      simp only [map_mul, norm_mul] at hn
      have h1 : ‖φ (algebraMap (𝓞 E) E r)‖ < 1 := (hφ r).2.mpr hr
      rw [hunit s hs] at hn
      have hlt : ‖φ (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E d)‖ * ‖φ (algebraMap (𝓞 E) E r)‖ < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) he) h1
      linarith
    · exact ⟨r, s, hr, hrel r s hdr⟩

private theorem norm_le_one_of_isIntegral_int' {l : ℕ} [Fact l.Prime] (z : Om l)
    (hz : IsIntegral ℤ z) : ‖z‖ ≤ 1 := by
  obtain ⟨p, hmon, hp⟩ := hz
  by_contra hgt
  push_neg at hgt
  have hcoef : ∀ c : ℤ, ‖(c : Om l)‖ ≤ 1 := fun c => by
    first
      | exact IsUltrametricDist.norm_intCast_le_one (Om l) c
      | exact IsUltrametricDist.norm_intCast_le_one c
      | (rcases Int.eq_nat_or_neg c with ⟨m, rfl | rfl⟩ <;>
          simp [IsUltrametricDist.norm_natCast_le_one])
  rw [hmon.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X_pow, eq_intCast] at hp
  have hcast : ∀ c : ℤ, Polynomial.eval₂ (algebraMap ℤ (Om l)) z (c : Polynomial ℤ) = (c : Om l) :=
    fun c => map_intCast (Polynomial.eval₂RingHom (algebraMap ℤ (Om l)) z) c
  simp only [hcast] at hp
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at hp
    simp at hp
  · have hsum : ‖∑ i ∈ Finset.range p.natDegree, ((p.coeff i : ℤ) : Om l) * z ^ i‖ ≤
        ‖z‖ ^ (p.natDegree - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      have hi' : i ≤ p.natDegree - 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [norm_mul, norm_pow]
      calc ‖((p.coeff i : ℤ) : Om l)‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ (p.natDegree - 1) :=
            mul_le_mul (hcoef _) (pow_le_pow_right₀ hgt.le hi') (by positivity) zero_le_one
        _ = ‖z‖ ^ (p.natDegree - 1) := one_mul _
    have heq : z ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, ((p.coeff i : ℤ) : Om l) * z ^ i :=
      eq_neg_of_add_eq_zero_left hp
    have hn : ‖z ^ p.natDegree‖ ≤ ‖z‖ ^ (p.natDegree - 1) := by
      rw [heq, norm_neg]
      exact hsum
    rw [norm_pow] at hn
    have hlt : ‖z‖ ^ (p.natDegree - 1) < ‖z‖ ^ p.natDegree := pow_lt_pow_right₀ hgt (by omega)
    linarith

theorem denseSurj : DenseSurj := by
  intro l _ E _ _ φ K hK hcl y hy hy1
  classical
  have hint : ∀ x : 𝓞 E, ‖φ (algebraMap (𝓞 E) E x)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral_int' _ ((x.isIntegral_coe).map φ.toIntAlgHom)
  have hl0 : ((l : ℕ) : Om l) ≠ 0 := by
    have hE : ((l : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    rw [← map_natCast φ l]
    exact (map_ne_zero φ).mpr hE
  have hr0 : 0 < ‖((l : ℕ) : Om l)‖ := norm_pos_iff.mpr hl0
  have hrlt : ‖((l : ℕ) : Om l)‖ < 1 := by
    have h1 : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) ((l : ℕ) : ℚ_[l]) := (map_natCast _ l).symm
    rw [h1]
    first
      | (rw [PadicAlgCl.norm_extends]; first | exact Padic.norm_p_lt_one | exact padicNormE.norm_p_lt_one)
      | (erw [PadicAlgCl.norm_extends]; first | exact Padic.norm_p_lt_one | exact padicNormE.norm_p_lt_one)
  obtain ⟨_, ⟨e, rfl⟩, he⟩ := Metric.mem_closure_iff.mp (hcl hy) _ hr0
  rw [dist_eq_norm] at he
  have hφe : ‖φ e‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max y (φ e - y)
    rw [add_sub_cancel] at h
    have h' : ‖φ e - y‖ ≤ 1 := by
      rw [norm_sub_rev]
      linarith
    exact h.trans (max_le hy1 h')
  let P : Ideal (𝓞 E) :=
    { carrier := {x | ‖φ (algebraMap (𝓞 E) E x)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at hx ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint c)) hx }
  have hP : ∀ x, x ∈ P ↔ ‖φ (algebraMap (𝓞 E) E x)‖ < 1 := fun x => Iff.rfl
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : 𝓞 E) ∈ P := by
        rw [htop]
        exact Submodule.mem_top
      rw [hP, map_one, map_one, norm_one] at h1
      exact lt_irrefl _ h1
    · intro a b hab
      rw [hP, map_mul, map_mul, norm_mul] at hab
      by_contra hcon
      simp only [not_or, hP, not_lt] at hcon
      obtain ⟨ha, hb⟩ := hcon
      have hm := mul_le_mul ha hb zero_le_one (norm_nonneg _)
      rw [one_mul] at hm
      linarith
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hlP : ((l : ℕ) : 𝓞 E) ∈ P := by
      rw [hP, map_natCast, map_natCast]
      exact hrlt
    rw [hbot, Ideal.mem_bot] at hlP
    have hlE := congrArg (algebraMap (𝓞 E) E) hlP
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at hlE
    exact (Fact.out : l.Prime).ne_zero hlE
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hPprime, hPne⟩
  have hφv : ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal) :=
    fun x => ⟨hint x, (hP x).symm⟩
  obtain ⟨s, a, hs, hes⟩ := exists_den φ v hφv e hφe
  let I : Ideal (𝓞 E) :=
    { carrier := {x | ‖φ (algebraMap (𝓞 E) E x)‖ ≤ ‖((l : ℕ) : Om l)‖}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at hx ⊢
        exact (mul_le_of_le_one_left (norm_nonneg _) (hint c)).trans hx }
  have hI : ∀ x, x ∈ I ↔ ‖φ (algebraMap (𝓞 E) E x)‖ ≤ ‖((l : ℕ) : Om l)‖ := fun x => Iff.rfl
  have hcop : Ideal.span {s} ⊔ I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hPm : P ≤ m := by
      intro x hx
      rw [hP] at hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr0 hx
      have hxn : x ^ n ∈ I := by
        rw [hI, map_pow, map_pow, norm_pow]
        exact hn.le
      exact hm.isPrime.mem_of_pow_mem n (hle (Ideal.mem_sup_right hxn))
    have hPeq : v.asIdeal = m := v.isMaximal.eq_of_le hm.ne_top hPm
    have hsm : s ∈ m := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self s))
    rw [← hPeq] at hsm
    exact hs hsm
  have h1mem : (1 : 𝓞 E) ∈ Ideal.span {s} ⊔ I := by
    rw [hcop]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp h1mem
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  have hwI := (hI w).mp hw
  have hw' : w = 1 - t * s := by
    rw [← huw]
    ring
  have hkey : φ e - φ (algebraMap (𝓞 E) E (a * t)) = φ e * φ (algebraMap (𝓞 E) E w) := by
    rw [hw']
    simp only [map_sub, map_one, map_mul]
    rw [← hes]
    simp only [map_mul]
    ring
  refine ⟨a * t, ?_⟩
  show ‖y - φ (algebraMap (𝓞 E) E (a * t))‖ ≤ ‖((l : ℕ) : Om l)‖
  have h1 : ‖φ e - φ (algebraMap (𝓞 E) E (a * t))‖ ≤ ‖((l : ℕ) : Om l)‖ := by
    rw [hkey, norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hφe) hwI
  have h2 : y - φ (algebraMap (𝓞 E) E (a * t)) =
      (y - φ e) + (φ e - φ (algebraMap (𝓞 E) E (a * t))) := by ring
  rw [h2]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le he.le h1)

end PI.CompDegEF
