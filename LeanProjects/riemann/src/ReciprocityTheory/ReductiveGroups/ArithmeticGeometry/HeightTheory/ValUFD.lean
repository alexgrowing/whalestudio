import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValUFD

variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]

theorem heightOne_principal (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ g : R, Prime g ∧ p = Ideal.span {g} := by
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
  have hsp : Ideal.span {Submodule.IsPrincipal.generator p} = p :=
    Submodule.IsPrincipal.span_singleton_generator p
  have hne : Submodule.IsPrincipal.generator p ≠ 0 := fun h0 =>
    p.ne_bot_of_height_eq_one hp ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)
  refine ⟨_, (Ideal.span_singleton_prime hne).mp (by rw [hsp]; infer_instance), hsp.symm⟩

theorem height_span_prime {q : R} (hq : Prime q) : (Ideal.span {q}).height = 1 := by
  have _ : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  apply le_antisymm
  · rw [← Nat.cast_one, Ideal.height_le_iff]
    intro P hPp hlt
    have hPb : P = ⊥ := by
      by_contra hne
      obtain ⟨q', hq'P, hq'⟩ := hPp.exists_mem_prime_of_ne_bot hne
      have hdvd : q ∣ q' := Ideal.mem_span_singleton.mp (hlt.le hq'P)
      have hass := hq.associated_of_dvd hq' hdvd
      have hle : Ideal.span {q} ≤ P :=
        (Ideal.span_singleton_le_iff_mem P).mpr (P.mem_of_dvd hass.symm.dvd hq'P)
      exact absurd hle (not_le_of_gt hlt)
    rw [hPb, Ideal.height_bot]
    exact_mod_cast Nat.zero_lt_one
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact hq.ne_zero

theorem loc_dvr (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g}) :
    IsDiscreteValuationRing (Localization.AtPrime p) ∧
      Irreducible (algebraMap R (Localization.AtPrime p) g) := by
  set O := Localization.AtPrime p
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hp (by rw [hg, Ideal.span_singleton_eq_bot])
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg ▸ inferInstance)
  have hinj : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors p)
  have h1 : Ideal.map (algebraMap R O) p = Ideal.span {algebraMap R O g} := by
    rw [congrArg (Ideal.map (algebraMap R O)) hg, Ideal.map_span, Set.image_singleton]
  have hspan : Ideal.span {algebraMap R O g} = IsLocalRing.maximalIdeal O :=
    h1.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p O)
  have hϖ0 : algebraMap R O g ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hg0
  have hϖ : Prime (algebraMap R O g) :=
    (Ideal.span_singleton_prime hϖ0).mp (by rw [hspan]; infer_instance)
  have hdvr : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨_, hϖ.irreducible, ?_⟩
    intro x hx
    obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.mk'_surjective p.primeCompl x
    simp only at hxs
    subst hxs
    have ha : a ≠ 0 := by rintro rfl; exact hx (by simp)
    obtain ⟨n, a', hnd, rfl⟩ := WfDvdMonoid.max_power_factor ha hgp.irreducible
    have ha' : a' ∈ p.primeCompl := by
      show a' ∉ p
      rw [hg, Ideal.mem_span_singleton]; exact hnd
    refine ⟨n, ((IsLocalization.AtPrime.isUnit_mk'_iff O p a' s).mpr ha').unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact ⟨hdvr, hϖ.irreducible⟩

theorem isUnit_mvPolynomial {σ K : Type*} [Field K] (κ : MvPolynomial σ K) (h : IsUnit κ) :
    ∃ k : K, k ≠ 0 ∧ κ = MvPolynomial.C k := by
  obtain ⟨r, hr, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
  exact ⟨r, hr.ne_zero, rfl⟩

section Factor

variable {gen : Ideal R → R}

theorem gen_prime (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) : Prime (gen p) := by
  obtain ⟨hpp, hh⟩ := hp
  have hg := hgen p hpp hh
  have hne : gen p ≠ 0 := by
    intro h0
    apply p.ne_bot_of_height_eq_one hh
    rw [hg, h0, Ideal.span_singleton_eq_bot]
  exact (Ideal.span_singleton_prime hne).mp (hg ▸ hpp)

theorem gen_dvd_iff (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) {q : R} (hq : Prime q) :
    gen p ∣ q ↔ p = Ideal.span {q} := by
  constructor
  · intro h
    rw [hgen p hp.1 hp.2, Ideal.span_singleton_eq_span_singleton]
    exact (gen_prime hgen hp).associated_of_dvd hq h
  · intro h
    subst h
    have h2 := hgen _ hp.1 hp.2
    rw [Ideal.span_singleton_eq_span_singleton] at h2
    exact h2.symm.dvd

theorem mult_prime (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) {q : R} (hq : Prime q) :
    multiplicity (gen p) q = if p = Ideal.span {q} then 1 else 0 := by
  split_ifs with h
  · have hass : Associated (gen p) q :=
      (gen_prime hgen hp).associated_of_dvd hq ((gen_dvd_iff hgen hp hq).mpr h)
    rw [multiplicity_eq_of_associated_left hass.symm, multiplicity_self]
  · exact multiplicity_eq_zero.mpr fun hd => h ((gen_dvd_iff hgen hp hq).mp hd)

theorem factor_int (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    (r : R) (hr : r ≠ 0) :
    ({p : Ideal R | p.IsPrime ∧ p.height = 1} ∩ {p | multiplicity (gen p) r ≠ 0}).Finite ∧
      ∃ κ : R, IsUnit κ ∧ algebraMap R F r = algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}),
          algebraMap R F (gen p) ^ (multiplicity (gen p) r : ℤ) := by
  classical
  set H := {p : Ideal R | p.IsPrime ∧ p.height = 1} with hH
  revert hr
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun r : R => r ≠ 0 →
    (H ∩ {p | multiplicity (gen p) r ≠ 0}).Finite ∧
      ∃ κ : R, IsUnit κ ∧ algebraMap R F r = algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ H), algebraMap R F (gen p) ^ (multiplicity (gen p) r : ℤ))
    r ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro x hx _
    have h0 : ∀ p ∈ H, multiplicity (gen p) x = 0 := fun p hp =>
      multiplicity_of_isUnit_right (gen_prime hgen hp).not_isUnit hx
    refine ⟨Set.finite_empty.subset fun p ⟨hp, hs⟩ => hs (h0 p hp), x, hx, ?_⟩
    rw [finprod_mem_of_eqOn_one (fun p hp => by simp [h0 p hp]), mul_one]
  · intro a q ha hq ih _
    obtain ⟨hfin, κ, hκ, heq⟩ := ih ha
    set p₀ := Ideal.span {q} with hp₀def
    have hp₀ : p₀ ∈ H :=
      ⟨(Ideal.span_singleton_prime hq.ne_zero).mpr hq, height_span_prime hq⟩
    have hmul : ∀ p ∈ H, multiplicity (gen p) (q * a) =
        (if p = p₀ then 1 else 0) + multiplicity (gen p) a := by
      intro p hp
      rw [multiplicity_mul (gen_prime hgen hp) (FiniteMultiplicity.of_prime_left (gen_prime hgen hp)
        (mul_ne_zero hq.ne_zero ha)), mult_prime hgen hp hq]
    have hGne : ∀ p ∈ H, algebraMap R F (gen p) ≠ 0 := fun p hp => by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R F)]; exact (gen_prime hgen hp).ne_zero
    have hsplit : ∀ p ∈ H, algebraMap R F (gen p) ^ (multiplicity (gen p) (q * a) : ℤ) =
        (if p = p₀ then algebraMap R F (gen p₀) else 1) *
          algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ) := by
      intro p hp
      rw [hmul p hp, Nat.cast_add, zpow_add₀ (hGne p hp)]
      split_ifs with h
      · rw [h, Nat.cast_one, zpow_one]
      · rw [Nat.cast_zero, zpow_zero]
    have hfin1 : (H ∩ Function.mulSupport
        (fun p => if p = p₀ then algebraMap R F (gen p₀) else 1)).Finite :=
      (Set.finite_singleton p₀).subset fun p ⟨_, hs⟩ => by
        by_contra h; exact hs (if_neg h)
    have hfin2 : (H ∩ Function.mulSupport
        (fun p => algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ))).Finite :=
      hfin.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp only [h0]; simp)⟩
    have hsingle : ∏ᶠ (p : Ideal R) (_ : p ∈ H),
        (if p = p₀ then algebraMap R F (gen p₀) else 1) = algebraMap R F (gen p₀) := by
      rw [finprod_eq_single _ p₀ (fun p hp => by simp [hp]), finprod_eq_if, if_pos hp₀, if_pos rfl]
    have hprod : ∏ᶠ (p : Ideal R) (_ : p ∈ H),
        algebraMap R F (gen p) ^ (multiplicity (gen p) (q * a) : ℤ) =
        algebraMap R F (gen p₀) * ∏ᶠ (p : Ideal R) (_ : p ∈ H),
          algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ) := by
      rw [finprod_mem_congr rfl hsplit, finprod_mem_mul_distrib' hfin1 hfin2, hsingle]
    refine ⟨((Set.finite_singleton p₀).union hfin).subset ?_, ?_⟩
    · rintro p ⟨hp, hs⟩
      by_cases h : p = p₀
      · exact Or.inl h
      · refine Or.inr ⟨hp, ?_⟩
        have := hmul p hp
        rw [if_neg h, zero_add] at this
        rw [Set.mem_ofPred_eq, ← this]; exact hs
    · have hass : Associated q (gen p₀) := by
        rw [← Ideal.span_singleton_eq_span_singleton]; exact hgen p₀ hp₀.1 hp₀.2
      obtain ⟨u, hu⟩ := hass
      refine ⟨↑u⁻¹ * κ, (Units.isUnit _).mul hκ, ?_⟩
      rw [hprod, ← hu, map_mul, heq, map_mul, map_mul]
      have hu1 : algebraMap R F ↑u⁻¹ * algebraMap R F ↑u = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(algebraMap R F q * algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ H), algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ))) * hu1

theorem factor_of_local (gen : Ideal R → R)
    (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    (z : F) (hz : z ≠ 0) (n : Ideal R → ℤ)
    (hn : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ a s : R, a ∉ p ∧ s ∉ p ∧
      z * algebraMap R F s = algebraMap R F (gen p) ^ n p * algebraMap R F a) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ n p ≠ 0}.Finite ∧
      ∃ κ : R, IsUnit κ ∧
        z = algebraMap R F κ *
          ∏ᶠ (p : Ideal R) (_ : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}),
            algebraMap R F (gen p) ^ n p := by
  classical
  set H := {p : Ideal R | p.IsPrime ∧ p.height = 1} with hH
  have hinj := IsFractionRing.injective R F
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) z
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : algebraMap R F y ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hy0
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero, zero_div] at hxy; exact hz hxy.symm
  have hzx : z * algebraMap R F y = algebraMap R F x := by rw [← hxy, div_mul_cancel₀ _ hyF]
  have hloc : ∀ p ∈ H, n p = (multiplicity (gen p) x : ℤ) - multiplicity (gen p) y := by
    intro p hp
    obtain ⟨a, s, ha, hs, he⟩ := hn p hp.1 hp.2
    have hg := gen_prime hgen hp
    have hgp := hgen p hp.1 hp.2
    have hna : ¬ gen p ∣ a := fun h => ha (by rw [hgp]; exact Ideal.mem_span_singleton.mpr h)
    have hns : ¬ gen p ∣ s := fun h => hs (by rw [hgp]; exact Ideal.mem_span_singleton.mpr h)
    have ha0 : a ≠ 0 := by rintro rfl; exact hna (dvd_zero _)
    have hs0 : s ≠ 0 := by rintro rfl; exact hns (dvd_zero _)
    have hGne : algebraMap R F (gen p) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hinj]; exact hg.ne_zero
    have h1 : algebraMap R F (gen p) ^ (n p).toNat =
        algebraMap R F (gen p) ^ n p * algebraMap R F (gen p) ^ (-n p).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hGne]; congr 1; omega
    have hR : x * s * gen p ^ (-n p).toNat = y * a * gen p ^ (n p).toNat := by
      apply hinj
      simp only [map_mul, map_pow]
      rw [h1, ← hzx]
      linear_combination (algebraMap R F y * algebraMap R F (gen p) ^ (-n p).toNat) * he
    have hm := congrArg (multiplicity (gen p)) hR
    have hf : ∀ b : R, b ≠ 0 → FiniteMultiplicity (gen p) b := fun b hb =>
      FiniteMultiplicity.of_prime_left hg hb
    have hpw : ∀ k : ℕ, gen p ^ k ≠ 0 := fun k => pow_ne_zero k hg.ne_zero
    rw [multiplicity_mul hg (hf _ (mul_ne_zero (mul_ne_zero hx0 hs0) (hpw _))),
      multiplicity_mul hg (hf _ (mul_ne_zero hx0 hs0)),
      multiplicity_mul hg (hf _ (mul_ne_zero (mul_ne_zero hy0 ha0) (hpw _))),
      multiplicity_mul hg (hf _ (mul_ne_zero hy0 ha0)),
      multiplicity_pow_self_of_prime hg, multiplicity_pow_self_of_prime hg,
      multiplicity_eq_zero.mpr hns, multiplicity_eq_zero.mpr hna] at hm
    omega
  obtain ⟨hfx, κx, hκx, hx⟩ := factor_int (F := F) hgen x hx0
  obtain ⟨hfy, κy, hκy, hyq⟩ := factor_int (F := F) hgen y hy0
  have hfinn : {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ n p ≠ 0}.Finite := by
    refine (hfx.union hfy).subset ?_
    rintro p ⟨h1, h2, h3⟩
    rw [hloc p ⟨h1, h2⟩] at h3
    by_cases hx' : multiplicity (gen p) x = 0
    · refine Or.inr ⟨⟨h1, h2⟩, fun h => h3 ?_⟩
      rw [hx', h]; simp
    · exact Or.inl ⟨⟨h1, h2⟩, hx'⟩
  refine ⟨hfinn, ?_⟩
  set fn : Ideal R → F := fun p => algebraMap R F (gen p) ^ n p with hfn
  set fy : Ideal R → F := fun p => algebraMap R F (gen p) ^ (multiplicity (gen p) y : ℤ) with hfy'
  have hsp : ∀ p ∈ H, algebraMap R F (gen p) ^ (multiplicity (gen p) x : ℤ) = fn p * fy p := by
    intro p hp
    have hGne : algebraMap R F (gen p) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hinj]; exact (gen_prime hgen hp).ne_zero
    simp only [hfn, hfy']
    rw [← zpow_add₀ hGne, hloc p hp]; congr 1; ring
  have hfin1 : (H ∩ Function.mulSupport fn).Finite :=
    hfinn.subset fun p ⟨hp, hs⟩ => ⟨hp.1, hp.2, fun h0 => hs (by simp [hfn, h0])⟩
  have hfin2 : (H ∩ Function.mulSupport fy).Finite :=
    hfy.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [hfy', h0])⟩
  have hPx : ∏ᶠ (p : Ideal R) (_ : p ∈ H),
      algebraMap R F (gen p) ^ (multiplicity (gen p) x : ℤ) =
      (∏ᶠ (p : Ideal R) (_ : p ∈ H), fn p) * ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p := by
    rw [finprod_mem_congr rfl hsp, finprod_mem_mul_distrib' hfin1 hfin2]
  rw [hPx] at hx
  have hyq' : algebraMap R F y = algebraMap R F κy * ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p := hyq
  have hPy : (∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hyq'; exact hyF hyq'
  have hκy0 : algebraMap R F κy ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hκy.ne_zero
  refine ⟨κx * ↑hκy.unit⁻¹, hκx.mul (Units.isUnit _), ?_⟩
  have hu1 : algebraMap R F κy * algebraMap R F ↑hκy.unit⁻¹ = 1 := by
    have h2 : κy * ↑hκy.unit⁻¹ = 1 := by simp
    rw [← map_mul, h2, map_one]
  apply mul_right_cancel₀ (mul_ne_zero hκy0 hPy)
  have e1 : z * (algebraMap R F κy * ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p) = algebraMap R F x := by
    rw [← hyq', hzx]
  rw [e1, hx, map_mul]
  linear_combination (-(algebraMap R F κx * (∏ᶠ (p : Ideal R) (_ : p ∈ H), fn p) *
    ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p)) * hu1

end Factor

end ValUFD

end ReciprocityTheory.ChartRestriction.G.T0
