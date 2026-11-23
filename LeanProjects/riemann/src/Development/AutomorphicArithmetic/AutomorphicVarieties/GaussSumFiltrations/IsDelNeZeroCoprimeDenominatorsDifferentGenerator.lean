import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HilbertThetaSeries.DenP
variable {F : Type} [Field F] [NumberField F]

theorem val_nat (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) : w.valuation F (n : F) = w.intValuation (n : 𝓞 F) := by
  rw [← map_natCast (algebraMap (𝓞 F) F) n, HeightOneSpectrum.valuation_of_algebraMap]

theorem isIntegral_iff_val (x : F) : IsIntegral ℤ x ↔ ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1 := by
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · have := w.valuation_le_one (K := F) (⟨x, h⟩ : 𝓞 F)
    exact this
  · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
    rw [← hr]; exact RingOfIntegers.isIntegral_coe r

theorem not_mem_of_coprime {p N : ℕ} (hc : N.Coprime p) {w : HeightOneSpectrum (𝓞 F)}
    (hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((N : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : ((u : 𝓞 F) * (N : 𝓞 F) + (v : 𝓞 F) * (p : 𝓞 F)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) huv
    push_cast at this
    exact this
  have : (1 : 𝓞 F) ∈ w.asIdeal := by
    rw [← h1]; exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hN) (w.asIdeal.mul_mem_left _ hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem val_coprime {p N : ℕ} (hc : N.Coprime p) {w : HeightOneSpectrum (𝓞 F)}
    (hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.valuation F (N : F) = 1 := by
  rw [val_nat]; exact HeightOneSpectrum.intValuation_eq_one_iff.2 (not_mem_of_coprime hc hp)

theorem val_ordCompl {p : ℕ} (n : ℕ) {w : HeightOneSpectrum (𝓞 F)} (hp : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    w.valuation F ((n / p ^ n.factorization p : ℕ) : F) = w.valuation F (n : F) := by
  conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [Nat.cast_mul, map_mul, Nat.cast_pow, map_pow, val_nat w p, HeightOneSpectrum.intValuation_eq_one_iff.2 hp,
    one_pow, one_mul]

theorem exists_nat_mul (x : F) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : F) * x) := by
  have ha : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
  obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
  rw [zsmul_eq_mul] at hy
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · exact ⟨n, by simpa using hy0, by simpa using hy⟩
  · exact ⟨n, by simpa using hy0, by simpa using hy.neg⟩

theorem exists_away {p : ℕ} (hp : p.Prime) (x : F) : ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧
    ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → w.valuation F ((N : F) * x) ≤ 1 := by
  obtain ⟨D, hD0, hD⟩ := exists_nat_mul x
  refine ⟨D / p ^ D.factorization p, Nat.ordCompl_pos p hD0, (Nat.coprime_ordCompl hp hD0).symm, fun w hw => ?_⟩
  rw [map_mul, val_ordCompl D hw, ← map_mul]
  exact (isIntegral_iff_val _).1 hD w

theorem exists_place {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [← map_natCast (algebraMap ℤ (𝓞 F)) p, Algebra.norm_algebraMap,
      isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 F)).ne'] at h1
    exact (Nat.prime_iff_prime_int.1 hp).not_unit h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hmem)

theorem diff_ne : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot

theorem coe_diff_ne : (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 diff_ne

theorem count_diff (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) :=
  FractionalIdeal.count_coe F w diff_ne

theorem mem_diff_iff (x : F) : x ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ↔
    ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  rw [GlobalTheory.Idele.mem_iff_valuation_le coe_diff_ne]
  simp only [count_diff]

theorem trace_int {y : F} (h : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F y ≤ WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
    {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F (y * x) = n := by
  have h1 : y ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [GlobalTheory.Idele.mem_iff_valuation_le (inv_ne_zero coe_diff_ne)]
    intro w
    rw [FractionalIdeal.count_inv, count_diff, neg_neg]
    exact h w
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv, FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 F)⁰ F))] at h1
  obtain ⟨n, hn⟩ := h1 x ((FractionalIdeal.mem_one_iff _).2 ⟨⟨x, hx⟩, rfl⟩)
  exact ⟨n, by rw [← Algebra.traceForm_apply, ← hn]; simp⟩

end GlobalTheory.HilbertThetaSeries.DenP

open GlobalTheory.HilbertThetaSeries.DenP in

theorem GlobalTheory.HilbertThetaSeries.denominators_prime_to : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → δ ≠ 0 ∧ (∀ x : F, PInt p x → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsIntegral ℤ ((N : F) * x)) ∧ (∀ b : F, PInt p (δ * b) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ ∀ x : F, IsIntegral ℤ x → ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * b * x) = n) ∧ ∃ (d : 𝓞 F) (N : ℕ), d ∈ differentIdeal ℤ (𝓞 F) ∧ N.Coprime p ∧ 0 < N ∧ PUnit p ((d : F) / δ) := by
  intro F _ _ p hp δ hδ
  have h0 : δ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_place (F := F) hp
    rintro rfl
    have := hδ w hw
    rw [map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨h0, fun x hx => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp x
    refine ⟨N, hN0, hNc, (isIntegral_iff_val _).2 fun w => ?_⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, val_coprime hNc hw, one_mul]; exact hx w hw
    · exact hN w hw
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp b
    refine ⟨N, hN0, hNc, fun x hx => trace_int (fun w => ?_) hx⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, val_coprime hNc hw, one_mul]
      have h1 := hb w hw
      rw [map_mul, hδ w hw, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_one] at h1
      exact h1
    · refine (hN w hw).trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      positivity
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp δ
    set c : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 F)) with hc
    have hc0 : c ≠ 0 := fun h => diff_ne (Ideal.absNorm_eq_zero_iff.1 h)
    have hcm : (c : F) ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨c, Ideal.absNorm_mem _, map_natCast _ _⟩
    have hcc : (c / p ^ c.factorization p).Coprime p := (Nat.coprime_ordCompl hp hc0).symm
    have hm : ((c / p ^ c.factorization p : ℕ) : F) * ((N : F) * δ) ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [mem_diff_iff]
      intro w
      by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
      · rw [map_mul, map_mul, val_coprime hNc hw, val_coprime hcc hw, one_mul, one_mul, hδ w hw]
      · rw [map_mul, val_ordCompl c hw]
        simpa using mul_le_mul' ((mem_diff_iff _).1 hcm w) (hN w hw)
    obtain ⟨d, hd, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
    refine ⟨d, 1, hd, Nat.coprime_one_left p, one_pos, fun w hw => ?_⟩
    have : (d : F) / δ = ((c / p ^ c.factorization p : ℕ) : F) * (N : F) := by
      rw [div_eq_iff h0, mul_assoc]; exact hd'
    rw [this, map_mul, val_coprime hNc hw, val_coprime hcc hw, one_mul]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDel_ne_zero_coprime_denominators_different_generator : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → δ ≠ 0 ∧ (∀ x : F, PInt p x → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsIntegral ℤ ((N : F) * x)) ∧ (∀ b : F, PInt p (δ * b) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ ∀ x : F, IsIntegral ℤ x → ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * b * x) = n) ∧ ∃ (d : 𝓞 F) (N : ℕ), d ∈ differentIdeal ℤ (𝓞 F) ∧ N.Coprime p ∧ 0 < N ∧ PUnit p ((d : F) / δ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.denominators_prime_to | exact GlobalTheory.HilbertThetaSeries.denominators_prime_to | (intros; apply GlobalTheory.HilbertThetaSeries.denominators_prime_to <;> assumption)
