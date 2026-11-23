import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem isIntAf_iff_val {p : ℕ} (x : AfP p) :
    IsIntAf x ↔ ∀ v : AwayP p, Valued.v (AfP.eval v x) ≤ 1 := by
  simp only [IsIntAf, mem_adicCompletionIntegers]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem val_algebraMap {p : ℕ} (v : AwayP p) (q : ℚ) :
    Valued.v (AfP.eval v (algebraMap ℚ (AfP p) q)) = v.1.valuation ℚ q := by
  rw [AlgHom.commutes]
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe ℚ v.1 q

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem val_nat_eq_one (v : HeightOneSpectrum ℤ) {n : ℕ} (h : (n : ℤ) ∉ v.asIdeal) :
    v.valuation ℚ (n : ℚ) = 1 := by
  have e : (n : ℚ) = algebraMap ℤ ℚ (n : ℤ) := by simp
  rw [e, valuation_of_algebraMap]
  exact intValuation_eq_one_iff.mpr h

private theorem lt_one_mul_exp_le {t : WithZero (Multiplicative ℤ)} (h : t < 1) :
    t * WithZero.exp (1 : ℤ) ≤ 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht] at h ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero (M := ℤ), WithZero.exp_le_exp]
    rw [← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp] at h
    omega

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem exists_gen (v : HeightOneSpectrum ℤ) :
    ∃ l : ℕ, 1 < l ∧ v.asIdeal = Ideal.span {(l : ℤ)} := by
  have hspan : v.asIdeal = Ideal.span {Submodule.IsPrincipal.generator v.asIdeal} :=
    (Ideal.span_singleton_generator v.asIdeal).symm
  refine ⟨(Submodule.IsPrincipal.generator v.asIdeal).natAbs, ?_, by rw [Int.span_natAbs]; exact hspan⟩
  have h0 : Submodule.IsPrincipal.generator v.asIdeal ≠ 0 := by
    intro h
    apply v.ne_bot
    rw [hspan, h, Ideal.span_singleton_eq_bot.mpr rfl]
  have h1 : (Submodule.IsPrincipal.generator v.asIdeal).natAbs ≠ 1 := by
    intro h
    apply v.isPrime.ne_top
    rw [hspan, ← Int.span_natAbs, h, Nat.cast_one, Ideal.span_singleton_one]
  have := Int.natAbs_pos.mpr h0
  omega

private theorem adjust (p : ℕ) [Fact p.Prime] (r : ℚ) (hr : 0 < r) :
    ∃ (n : ℤ) (a b : ℕ), 0 < a ∧ 0 < b ∧ a.Coprime p ∧ b.Coprime p ∧
      r * (p : ℚ) ^ n * a = b := by
  have hp : p.Prime := Fact.out
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hnum0 : 0 < r.num := Rat.num_pos.mpr hr
  obtain ⟨e1, b, hb, hnum⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := r.num.toNat) (by omega) p hp1
  obtain ⟨e2, a, ha, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd r.den_nz p hp1
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, mul_zero] at hden
      exact absurd hden r.den_nz
    · exact h
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hnum
      omega
    · exact h
  refine ⟨(e2 : ℤ) - e1, a, b, ha0, hb0, ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha).symm,
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb).symm, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrn : r * ((p : ℚ) ^ e2 * a) = (p : ℚ) ^ e1 * b := by
    have h1 := Rat.mul_den_eq_num r
    have h2 : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
      have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum0.le
      exact_mod_cast this
    have hd : ((r.den : ℕ) : ℚ) = (p : ℚ) ^ e2 * a := by exact_mod_cast hden
    have hn : ((r.num.toNat : ℕ) : ℚ) = (p : ℚ) ^ e1 * b := by exact_mod_cast hnum
    rw [← hd, h1, ← h2, hn]
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination hrn

private theorem natCast_prime_not_mem_awayP {p : ℕ} [Fact p.Prime] (v : AwayP p) :
    ((p : ℕ) : ℤ) ∉ v.1.asIdeal := by
  intro hmem
  obtain ⟨l, hl, hspan⟩ := exists_gen v.1
  rw [hspan, Ideal.mem_span_singleton, Int.natCast_dvd_natCast] at hmem
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd l hmem with h | h
  · omega
  · exact v.2 (by rw [hspan, h])

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem valuation_generator_eq_exp_neg_one (v : HeightOneSpectrum ℤ) (l : ℕ) (hl : 1 < l)
    (hspan : v.asIdeal = Ideal.span {(l : ℤ)}) : v.valuation ℚ (l : ℚ) = WithZero.exp (-1) := by
  have e : (l : ℚ) = algebraMap ℤ ℚ (l : ℤ) := by simp
  have hl0 : (l : ℤ) ≠ 0 := by omega
  rw [e, valuation_of_algebraMap, v.intValuation_eq_exp_neg_multiplicity hl0, ← hspan,
    multiplicity_self]
  rfl

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem valuation_generator_other_eq_one (v w : HeightOneSpectrum ℤ) (l : ℕ)
    (hspan : v.asIdeal = Ideal.span {(l : ℤ)}) (hvw : v ≠ w) : w.valuation ℚ (l : ℚ) = 1 := by
  apply val_nat_eq_one
  intro hmem
  apply hvw
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem exists_pos_rat_valuation_one_away {p : ℕ} [Fact p.Prime] (K : ℕ) : ∀ (y : (AfP p)ˣ), 0 < K →
    IsIntAf (y : AfP p) → IsIntAf (algebraMap ℚ (AfP p) K * ((y⁻¹ : (AfP p)ˣ) : AfP p)) →
    ∃ s : ℚ, 0 < s ∧ ∀ v : AwayP p,
      Valued.v (AfP.eval v (algebraMap ℚ (AfP p) s * (y : AfP p))) = 1 := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
  intro y hK hy hKy
  by_cases hall : ∀ v : AwayP p, Valued.v (AfP.eval v (y : AfP p)) = 1
  · exact ⟨1, one_pos, fun v => by rw [map_one, one_mul]; exact hall v⟩
  push_neg at hall
  obtain ⟨v, hv⟩ := hall
  have hvlt : Valued.v (AfP.eval v (y : AfP p)) < 1 :=
    lt_of_le_of_ne ((isIntAf_iff_val _).mp hy v) hv
  obtain ⟨l, hl, hspan⟩ := exists_gen v.1
  have hlK : l ∣ K := by
    have hK1 : Valued.v (AfP.eval v (algebraMap ℚ (AfP p) K)) < 1 := by
      have e : algebraMap ℚ (AfP p) K =
          (y : AfP p) * (algebraMap ℚ (AfP p) K * ((y⁻¹ : (AfP p)ˣ) : AfP p)) := by
        rw [mul_left_comm, Units.mul_inv, mul_one]
      rw [e, map_mul, Valuation.map_mul]
      calc _ ≤ Valued.v (AfP.eval v (y : AfP p)) * 1 := by
            gcongr
            exact (isIntAf_iff_val _).mp hKy v
        _ < 1 := by rw [mul_one]; exact hvlt
    rw [val_algebraMap] at hK1
    have e2 : (K : ℚ) = algebraMap ℤ ℚ (K : ℤ) := by simp
    rw [e2, valuation_lt_one_iff_mem, hspan, Ideal.mem_span_singleton,
      Int.natCast_dvd_natCast] at hK1
    exact hK1
  obtain ⟨K', rfl⟩ := hlK
  have hK' : 0 < K' := Nat.pos_of_ne_zero (by rintro rfl; simp at hK)
  have hK'lt : K' < l * K' := by nlinarith
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hlu : IsUnit (algebraMap ℚ (AfP p) (l : ℚ)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hl0)).map _
  have hy'val : ((y * hlu.unit : (AfP p)ˣ) : AfP p) = algebraMap ℚ (AfP p) (l : ℚ)⁻¹ * y := by
    rw [Units.val_mul, IsUnit.unit_spec, mul_comm]
  have hy' : IsIntAf ((y * hlu.unit : (AfP p)ˣ) : AfP p) := by
    rw [isIntAf_iff_val]
    intro w
    rw [hy'val, map_mul, Valuation.map_mul, val_algebraMap, map_inv₀]
    by_cases hw : w = v
    · subst hw
      rw [valuation_generator_eq_exp_neg_one _ l hl hspan, ← WithZero.exp_neg, neg_neg, mul_comm]
      exact lt_one_mul_exp_le hvlt
    · rw [valuation_generator_other_eq_one v.1 w.1 l hspan (fun h => hw (Subtype.ext h).symm), inv_one, one_mul]
      exact (isIntAf_iff_val _).mp hy w
  have hinv : (((y * hlu.unit)⁻¹ : (AfP p)ˣ) : AfP p) =
      algebraMap ℚ (AfP p) (l : ℚ) * ((y⁻¹ : (AfP p)ˣ) : AfP p) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hy'val]
    calc algebraMap ℚ (AfP p) (l : ℚ)⁻¹ * (y : AfP p) *
          (algebraMap ℚ (AfP p) (l : ℚ) * ((y⁻¹ : (AfP p)ˣ) : AfP p))
        = algebraMap ℚ (AfP p) ((l : ℚ)⁻¹ * l) * ((y : AfP p) * ((y⁻¹ : (AfP p)ˣ) : AfP p)) := by
          rw [map_mul]; ring
      _ = 1 := by rw [inv_mul_cancel₀ hl0, map_one, Units.mul_inv, one_mul]
  have hKy' : IsIntAf (algebraMap ℚ (AfP p) K' *
      (((y * hlu.unit)⁻¹ : (AfP p)ˣ) : AfP p)) := by
    have e : algebraMap ℚ (AfP p) K' * (((y * hlu.unit)⁻¹ : (AfP p)ˣ) : AfP p) =
        algebraMap ℚ (AfP p) ((l * K' : ℕ) : ℚ) * ((y⁻¹ : (AfP p)ˣ) : AfP p) := by
      rw [hinv]
      push_cast
      ring
    rw [e]
    exact hKy
  obtain ⟨s', hs', hval⟩ := ih K' hK'lt (y * hlu.unit) hK' hy' hKy'
  refine ⟨s' / l, div_pos hs' (by positivity), fun w => ?_⟩
  have e : algebraMap ℚ (AfP p) (s' / l) * (y : AfP p) =
      algebraMap ℚ (AfP p) s' * ((y * hlu.unit : (AfP p)ˣ) : AfP p) := by
    rw [hy'val, div_eq_mul_inv, map_mul]
    ring
  rw [e]
  exact hval w

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem scale {p : ℕ} [Fact p.Prime] (c : (AfP p)ˣ) :
    ∃ s₀ : ℚ, 0 < s₀ ∧ ∀ v : AwayP p,
      Valued.v (AfP.eval v (algebraMap ℚ (AfP p) s₀ * ((c⁻¹ : (AfP p)ˣ) : AfP p))) = 1 := by
  obtain ⟨N, hN, hNc⟩ := DenAway.exists_nat_adele ((c⁻¹ : (AfP p)ˣ) : AfP p)
  obtain ⟨M, hM, hMc⟩ := DenAway.exists_nat_adele (c : AfP p)
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hu : IsUnit (algebraMap ℚ (AfP p) (N : ℚ)) := (isUnit_iff_ne_zero.mpr hN0).map _
  have hyv : ((hu.unit * c⁻¹ : (AfP p)ˣ) : AfP p) =
      algebraMap ℚ (AfP p) N * ((c⁻¹ : (AfP p)ˣ) : AfP p) := by
    rw [Units.val_mul, IsUnit.unit_spec]
  have hy : IsIntAf ((hu.unit * c⁻¹ : (AfP p)ˣ) : AfP p) := by
    rw [hyv, map_natCast]
    exact hNc
  have hyinv : (((hu.unit * c⁻¹)⁻¹ : (AfP p)ˣ) : AfP p) =
      algebraMap ℚ (AfP p) (N : ℚ)⁻¹ * c := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hyv]
    calc algebraMap ℚ (AfP p) N * ((c⁻¹ : (AfP p)ˣ) : AfP p) * (algebraMap ℚ (AfP p) (N : ℚ)⁻¹ * c)
        = algebraMap ℚ (AfP p) ((N : ℚ) * (N : ℚ)⁻¹) * (((c⁻¹ : (AfP p)ˣ) : AfP p) * c) := by
          rw [map_mul]; ring
      _ = 1 := by rw [mul_inv_cancel₀ hN0, map_one, Units.inv_mul, one_mul]
  have hKy : IsIntAf (algebraMap ℚ (AfP p) ((N * M : ℕ) : ℚ) *
      (((hu.unit * c⁻¹)⁻¹ : (AfP p)ˣ) : AfP p)) := by
    have e : algebraMap ℚ (AfP p) ((N * M : ℕ) : ℚ) * (((hu.unit * c⁻¹)⁻¹ : (AfP p)ˣ) : AfP p) =
        (M : AfP p) * c := by
      rw [hyinv, ← mul_assoc, ← map_mul,
        show ((N * M : ℕ) : ℚ) * (N : ℚ)⁻¹ = ((M : ℕ) : ℚ) by push_cast; field_simp, map_natCast]
    rw [e]
    exact hMc
  obtain ⟨s, hs, hval⟩ := exists_pos_rat_valuation_one_away (N * M) (hu.unit * c⁻¹) (Nat.mul_pos hN hM) hy hKy
  refine ⟨s * N, mul_pos hs (by exact_mod_cast hN), fun v => ?_⟩
  have e : algebraMap ℚ (AfP p) (s * N) * ((c⁻¹ : (AfP p)ˣ) : AfP p) =
      algebraMap ℚ (AfP p) s * ((hu.unit * c⁻¹ : (AfP p)ˣ) : AfP p) := by
    rw [hyv, map_mul, mul_assoc]
  rw [e]
  exact hval v

theorem UpperTheory.exists_rat_unit_factorization_finiteAdelesAwayP :
    ∀ (p : ℕ) [Fact p.Prime] (c : (AfP p)ˣ) (s : ℚ), 0 < s → ∃ (s₁ : ℚ) (ε : (AfP p)ˣ) (a b : ℕ), 0 < s₁ ∧ IsIntAf (ε : AfP p) ∧ IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p) ∧ algebraMap ℚ (AfP p) s₁ = (ε : AfP p) * (c : AfP p) ∧ 0 < a ∧ 0 < b ∧ a.Coprime p ∧ b.Coprime p ∧ s₁ * a = s * b := by
  intro p _ c s hs
  have hp : p.Prime := Fact.out
  obtain ⟨s₀, hs₀, hval⟩ := scale c
  obtain ⟨n, a, b, ha, hb, hap, hbp, hab⟩ := adjust p (s₀ / s) (div_pos hs₀ hs)
  have hpn : (0 : ℚ) < (p : ℚ) ^ n := zpow_pos (by exact_mod_cast hp.pos) n
  have hs₁ : 0 < s₀ * (p : ℚ) ^ n := mul_pos hs₀ hpn
  have hu : IsUnit (algebraMap ℚ (AfP p) (s₀ * (p : ℚ) ^ n)) :=
    (isUnit_iff_ne_zero.mpr hs₁.ne').map _
  have hεv : ((hu.unit * c⁻¹ : (AfP p)ˣ) : AfP p) = algebraMap ℚ (AfP p) ((p : ℚ) ^ n) *
      (algebraMap ℚ (AfP p) s₀ * ((c⁻¹ : (AfP p)ˣ) : AfP p)) := by
    rw [Units.val_mul, IsUnit.unit_spec, map_mul]
    ring
  have hpv : ∀ v : AwayP p, Valued.v (AfP.eval v (algebraMap ℚ (AfP p) ((p : ℚ) ^ n))) = 1 := by
    intro v
    rw [val_algebraMap, map_zpow₀, val_nat_eq_one v.1 (natCast_prime_not_mem_awayP v), one_zpow]
  have h1 : ∀ v : AwayP p, Valued.v (AfP.eval v ((hu.unit * c⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    intro v
    rw [hεv, map_mul, Valuation.map_mul, hpv v, hval v, one_mul]
  refine ⟨s₀ * (p : ℚ) ^ n, hu.unit * c⁻¹, a, b, hs₁, ?_, ?_, ?_, ha, hb, hap, hbp, ?_⟩
  · rw [isIntAf_iff_val]
    intro v
    exact (h1 v).le
  · rw [isIntAf_iff_val]
    intro v
    have hm : Valued.v (AfP.eval v ((hu.unit * c⁻¹ : (AfP p)ˣ) : AfP p)) *
        Valued.v (AfP.eval v (((hu.unit * c⁻¹)⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
    rw [h1 v, one_mul] at hm
    exact hm.le
  · rw [Units.val_mul, IsUnit.unit_spec, mul_assoc, Units.inv_mul, mul_one]
  · have hs0 : s ≠ 0 := hs.ne'
    field_simp at hab
    linear_combination hab
