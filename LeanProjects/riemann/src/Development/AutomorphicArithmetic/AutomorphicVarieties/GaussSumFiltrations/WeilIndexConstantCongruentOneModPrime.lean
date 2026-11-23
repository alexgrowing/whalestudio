import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IsDelNeZeroCoprimeDenominatorsDifferentGenerator
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.DConst

variable {F : Type} [Field F] [NumberField F]

theorem absNorm_coprime_of_away {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 F))
    (hJ : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ¬ J ≤ w.asIdeal) :
    (Ideal.absNorm J).Coprime p := by
  classical
  obtain ⟨w0, hw0⟩ := DenP.exists_place (F := F) hp
  have hJ0 : J ≠ ⊥ := by rintro rfl; exact hJ w0 hw0 bot_le
  have hsup : J ⊔ Ideal.span {((p : ℕ) : 𝓞 F)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpM : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hM0 : M ≠ ⊥ := by rintro rfl; exact hp.ne_zero (by simpa using hpM)
    exact hJ ⟨M, hM.isPrime, hM0⟩ hpM (le_sup_left.trans hle)
  obtain ⟨a, ha, z, hz, haz⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : Ideal.absNorm J ≠ 0 := fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn0
  haveI : Finite (𝓞 F ⧸ J) := Nat.finite_of_card_ne_zero hn0
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (p : 𝓞 F ⧸ J) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have h2 : (Ideal.Quotient.mk J b) * (p : 𝓞 F ⧸ J) = 1 := by
    have := congrArg (Ideal.Quotient.mk J) haz
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, map_natCast, map_one] at this
    exact this
  have h3 : x = 0 := by
    calc x = (Ideal.Quotient.mk J b * (p : 𝓞 F ⧸ J)) * x := by rw [h2, one_mul]
      _ = 0 := by rw [mul_assoc, h1, mul_zero]
  rw [h3, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

theorem diff_cofactor {p : ℕ} (δ : F) (hδ : IsDel p δ) (d : 𝓞 F)
    (hd : d ∈ differentIdeal ℤ (𝓞 F)) (hu : PUnit p ((d : F) / δ)) :
    ∃ J : Ideal (𝓞 F), Ideal.span {d} = differentIdeal ℤ (𝓞 F) * J ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ¬ J ≤ w.asIdeal := by
  classical
  have hle : Ideal.span {d} ≤ differentIdeal ℤ (𝓞 F) := (Ideal.span_singleton_le_iff_mem _).2 hd
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  refine ⟨J, hJ, fun w hw hJw => ?_⟩
  have hv := hu w hw
  rw [map_div₀, hδ w hw, div_eq_one_iff_eq WithZero.exp_ne_zero] at hv
  have hv' : w.intValuation d = WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
    rw [← hv]; exact (HeightOneSpectrum.valuation_of_algebraMap (K := F) w d).symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ
    exact hd0 (Ideal.span_singleton_eq_bot.1 hJ)
  rw [w.intValuation_if_neg hd0, WithZero.exp_inj, neg_inj, Nat.cast_inj, hJ, ← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.2 DenP.diff_ne) (Associates.mk_ne_zero.2 hJ0)
      w.associates_irreducible] at hv'
  have hc := (Associates.count_ne_zero_iff_dvd hJ0 w.irreducible).2 (Ideal.dvd_iff_le.2 hJw)
  unfold ordI at hv'
  exact hc (by omega)

theorem norm_intCast_eq_natAbs {p : ℕ} [Fact p.Prime] (z : ℤ) :
    ‖((z : ℚ) : ℚ_[p])‖ = ‖((z.natAbs : ℚ) : ℚ_[p])‖ := by
  rcases Int.natAbs_eq z with h | h
  · have e : ((z : ℚ) : ℚ_[p]) = ((z.natAbs : ℚ) : ℚ_[p]) := by
      conv_lhs => rw [h]
      simp only [Int.cast_natCast]
    rw [e]
  · have e : ((z : ℚ) : ℚ_[p]) = -((z.natAbs : ℚ) : ℚ_[p]) := by
      conv_lhs => rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Rat.cast_neg]
    rw [e, norm_neg]

theorem norm_norm_eq_one {p : ℕ} [Fact p.Prime] (x : F) (hx : PUnit p x) :
    ‖((Algebra.norm ℚ x : ℚ) : ℚ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, hN0, hNc, hN⟩ := DenP.exists_away hp x
  have hint : IsIntegral ℤ ((N : F) * x) := (DenP.isIntegral_iff_val _).2 fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, DenP.val_coprime hNc hw, hx w hw, one_mul]
    · exact hN w hw
  let a : 𝓞 F := ⟨_, hint⟩
  have haF : (a : F) = (N : F) * x := rfl
  have ha : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ Ideal.span {a} ≤ w.asIdeal := by
    intro w hw hle
    have h1 : a ∈ w.asIdeal := hle (Ideal.mem_span_singleton_self a)
    have h2 : w.valuation F (algebraMap (𝓞 F) F a) = 1 := by
      show w.valuation F ((N : F) * x) = 1
      rw [map_mul, DenP.val_coprime hNc hw, hx w hw, one_mul]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff] at h2
    exact h2 h1
  have hc := absNorm_coprime_of_away hp _ ha
  rw [Ideal.absNorm_span_singleton] at hc
  have h1 : ‖(((Algebra.norm ℤ a : ℤ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [norm_intCast_eq_natAbs, Rat.cast_natCast, Padic.norm_natCast_eq_one_iff]
    exact hc.symm
  have hNn : Algebra.norm ℚ (N : F) = (N : ℚ) ^ Module.finrank ℚ F := by
    rw [← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap]
  rw [Algebra.coe_norm_int, haF, map_mul, hNn, Rat.cast_mul, norm_mul, Rat.cast_pow, norm_pow,
    Rat.cast_natCast, Padic.norm_natCast_eq_one_iff.2 hNc.symm, one_pow, one_mul] at h1
  exact h1

theorem norm_norm_eq_disc {p : ℕ} [Fact p.Prime] (δ c : F) (hδ : IsDel p δ) (hc : PUnit p (c / δ)) :
    ‖((Algebra.norm ℚ c : ℚ) : ℚ_[p])‖ = ‖(((discr F).natAbs : ℚ) : ℚ_[p])‖ := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ0, -, -, d, -, hd, -, -, hdu⟩ := denominators_prime_to F p hp δ hδ
  obtain ⟨J, hJ, hJw⟩ := diff_cofactor δ hδ d hd hdu
  have hd0 : (d : F) ≠ 0 := by
    obtain ⟨w, hw⟩ := DenP.exists_place (F := F) hp
    intro h
    have := hdu w hw
    rw [h, zero_div, map_zero] at this
    exact zero_ne_one this
  have hcd : PUnit p (c / d) := fun w hw => by
    have e : c / (d : F) = (c / δ) / ((d : F) / δ) := by field_simp
    rw [e, map_div₀, hc w hw, hdu w hw, div_one]
  have h1 := norm_norm_eq_one (p := p) _ hcd
  have e2 : c = c / d * d := by field_simp
  have hJc := absNorm_coprime_of_away hp J hJw
  have hnd : (Algebra.norm ℤ d).natAbs = (discr F).natAbs * Ideal.absNorm J := by
    rw [← Ideal.absNorm_span_singleton, hJ, map_mul, NumberField.absNorm_differentIdeal (K := F)]
  have h2 : ‖((Algebra.norm ℚ (d : F) : ℚ) : ℚ_[p])‖ = ‖(((discr F).natAbs : ℚ) : ℚ_[p])‖ := by
    rw [← Algebra.coe_norm_int, norm_intCast_eq_natAbs, hnd, Nat.cast_mul, Rat.cast_mul, norm_mul,
      Rat.cast_natCast (Ideal.absNorm J : ℕ), Padic.norm_natCast_eq_one_iff.2 hJc.symm, mul_one]
  rw [e2, map_mul, Rat.cast_mul, norm_mul, h1, one_mul, h2]

theorem norm_le_one_of_near {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹) : ‖x‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  calc ‖x‖ = ‖(x - 1) + 1‖ := by ring_nf
    _ ≤ max ‖x - 1‖ ‖(1 : ℚ_[p])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (hx.trans hp1) (by simp)

theorem near_mul {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹)
    (hy : ‖y - 1‖ ≤ (p : ℝ)⁻¹) : ‖x * y - 1‖ ≤ (p : ℝ)⁻¹ := by
  have h1 := norm_le_one_of_near hx
  calc ‖x * y - 1‖ = ‖x * (y - 1) + (x - 1)‖ := by ring_nf
    _ ≤ max ‖x * (y - 1)‖ ‖x - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ (p : ℝ)⁻¹ := by
      refine max_le ?_ hx
      rw [norm_mul]
      calc ‖x‖ * ‖y - 1‖ ≤ 1 * (p : ℝ)⁻¹ := by gcongr
        _ = (p : ℝ)⁻¹ := one_mul _

theorem near_pow {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖x ^ n - 1‖ ≤ (p : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact near_mul ih hx

theorem near_inv {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖x⁻¹ - 1‖ ≤ (p : ℝ)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hlt : ‖x - 1‖ < ‖(1 : ℚ_[p])‖ := by
    rw [norm_one]; exact hx.trans_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
  have hn : ‖x‖ = 1 := by rw [Padic.norm_eq_of_norm_sub_lt_right hlt, norm_one]
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have e : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
  rw [e, norm_mul, norm_neg, norm_inv, hn, inv_one, mul_one]
  exact hx

theorem fermat {p : ℕ} [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖ = 1) : ‖u ^ (p - 1) - 1‖ ≤ (p : ℝ)⁻¹ := by
  let v : ℤ_[p] := ⟨u, hu.le⟩
  have hv : ‖v‖ = 1 := hu
  have hz : PadicInt.toZMod v ≠ 0 := by
    intro h
    have h1 : v ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h
    have h2 := PadicInt.mem_nonunits.1 (IsLocalRing.mem_maximalIdeal _ |>.1 h1)
    rw [hv] at h2; exact lt_irrefl _ h2
  have h1 : PadicInt.toZMod (v ^ (p - 1) - 1) = 0 := by
    rw [map_sub, map_pow, ZMod.pow_card_sub_one_eq_one hz, map_one, sub_self]
  have h2 : ‖v ^ (p - 1) - 1‖ < 1 := by
    have h3 : v ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h1
    exact PadicInt.mem_nonunits.1 (IsLocalRing.mem_maximalIdeal _ |>.1 h3)
  obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h2
  have h4 : ‖v ^ (p - 1) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [hy, norm_mul, PadicInt.norm_p]
    calc (p : ℝ)⁻¹ * ‖y‖ ≤ (p : ℝ)⁻¹ * 1 := by gcongr; exact PadicInt.norm_le_one y
      _ = (p : ℝ)⁻¹ := mul_one _
  have e : ((v ^ (p - 1) - 1 : ℤ_[p]) : ℚ_[p]) = u ^ (p - 1) - 1 := by push_cast; rfl
  rw [← e]
  exact h4

end GlobalTheory.HilbertThetaSeries.DConst

open GlobalTheory.HilbertThetaSeries.DConst in

theorem GlobalTheory.HilbertThetaSeries.wC_near_one : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ c : F, IsDel p δ → PUnit p (c / δ) → ∀ t N : ℕ, N.Coprime p → (-1) ^ ((p - 1) / 2) * (t : ℤ) ≡ 1 [ZMOD p] → ‖ι.symm (wC (p - 1) t (N : F) c) - 1‖ ≤ (p : ℝ)⁻¹ := by
  intro F _ _ p _ ι hp2 δ c hδ hc t N hN ht
  have hp : p.Prime := Fact.out
  set n := Module.finrank ℚ F with hn
  set m := (p - 1) / 2 with hmdef
  have hm : p - 1 = 2 * m := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  set q : ℚ := Algebra.norm ℚ c / ((N : ℚ) ^ n) ^ 2 / ((discr F).natAbs : ℚ) with hq
  set R : ℚ := (-1) ^ (m * n) * (Algebra.norm ℚ c) ^ (p - 1) /
    (((N : ℚ) ^ n) ^ (2 * (p - 1)) * ((discr F).natAbs : ℚ) ^ (p - 1) * (t : ℚ) ^ n) with hR
  have hw : wC (p - 1) t (N : F) c = (R : ℂ) := by
    have hNn : Algebra.norm ℚ (N : F) = (N : ℚ) ^ n := by
      rw [← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap]
    have hI : (-Complex.I) ^ ((p - 1) * n) = (-1) ^ (m * n) := by
      rw [hm, mul_assoc, pow_mul, neg_sq, Complex.I_sq]
    unfold wC
    rw [hNn, hI, hR]
    push_cast
    ring
  have hQ : ι.symm (R : ℂ) - 1 = algebraMap ℚ_[p] (Qbar p) ((R : ℚ_[p]) - 1) := by
    rw [map_ratCast, map_sub, map_ratCast, map_one]
  rw [hw, hQ]
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) ((R : ℚ_[p]) - 1)‖ ≤ (p : ℝ)⁻¹
  rw [PadicAlgCl.norm_extends]
  have ht0 : (t : ℚ) ≠ 0 := by
    rintro h
    have h' : t = 0 := by exact_mod_cast h
    subst h'
    have := (Int.ModEq.dvd ht)
    simp at this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  have hN0 : (N : ℚ) ≠ 0 := by
    rintro h
    have h' : N = 0 := by exact_mod_cast h
    subst h'
    exact hp.one_lt.ne' (by simpa using hN)
  have hD0 : ((discr F).natAbs : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero F)
  have hε : ((-1 : ℚ) ^ m)⁻¹ = (-1) ^ m := by rw [← inv_pow, inv_neg, inv_one]
  have hRe : R = (((-1 : ℚ) ^ m * t)⁻¹) ^ n * q ^ (p - 1) := by
    rw [hR, hq, mul_inv, hε]
    ring
  have hr : ‖((((-1 : ℚ) ^ m * t : ℚ) : ℚ_[p])) - 1‖ ≤ (p : ℝ)⁻¹ := by
    have hd := Int.ModEq.dvd ht
    have h1 := (Padic.norm_int_le_pow_iff_dvd (p := p) (1 - (-1) ^ m * (t : ℤ)) 1).2 (by simpa using hd)
    have e : ((((-1 : ℚ) ^ m * t : ℚ) : ℚ_[p])) - 1 = -(((1 - (-1) ^ m * (t : ℤ) : ℤ) : ℚ_[p])) := by
      push_cast; ring
    rw [e, norm_neg]
    simpa using h1
  have hqn : ‖((q : ℚ) : ℚ_[p])‖ = 1 := by
    have hDn : ‖((discr F).natAbs : ℚ_[p])‖ ≠ 0 := by
      rw [norm_ne_zero_iff, Nat.cast_ne_zero]; exact Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero F)
    rw [hq, Rat.cast_div, Rat.cast_div, norm_div, norm_div, norm_norm_eq_disc δ c hδ hc]
    simp only [Rat.cast_pow, Rat.cast_natCast, norm_pow, Padic.norm_natCast_eq_one_iff.2 hN.symm,
      one_pow, div_one]
    exact div_self hDn
  rw [hRe, Rat.cast_mul, Rat.cast_pow, Rat.cast_pow, Rat.cast_inv]
  exact near_mul (near_pow (near_inv hr) n) (fermat _ hqn)

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_index_constant_congruent_one_mod_prime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ c : F, IsDel p δ → PUnit p (c / δ) → ∀ t N : ℕ, N.Coprime p → (-1) ^ ((p - 1) / 2) * (t : ℤ) ≡ 1 [ZMOD p] → ‖ι.symm (wC (p - 1) t (N : F) c) - 1‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.wC_near_one | exact GlobalTheory.HilbertThetaSeries.wC_near_one | (intros; apply GlobalTheory.HilbertThetaSeries.wC_near_one <;> assumption)
