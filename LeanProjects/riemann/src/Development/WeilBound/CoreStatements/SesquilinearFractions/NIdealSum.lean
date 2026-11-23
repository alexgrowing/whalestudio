import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealMulSpanMapStatement

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem logIdeal_pow (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p])
    (hj : Function.Injective j) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∀ n : ℕ, logIdeal j (I ^ n) = n * logIdeal j I := by
  intro n
  induction n with
  | zero =>
    have h1 := (GlobalTheory.T.log_ideal_mul_span_map E p j hj).2.1 1
    rw [Ideal.span_singleton_one, map_one, norm_one, Real.log_one] at h1
    simpa using h1
  | succ n ih =>
    rw [pow_succ, (GlobalTheory.T.log_ideal_mul_span_map E p j hj).1 _ _ (pow_ne_zero _ hI) hI, ih]
    push_cast
    ring

theorem sum_logIdeal_eq_log_absNorm : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) I = Real.log ‖((Ideal.absNorm I : ℕ) : ℂ_[p])‖ := by
  intro E _ _ I hI p
  classical
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hmem : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  have hprin : (I ^ h).IsPrincipal := by
    have hmem' : I ^ h ∈ nonZeroDivisors (Ideal (𝓞 E)) := pow_mem hmem h
    rw [← ClassGroup.mk0_eq_one_iff hmem']
    have e1 : (⟨I ^ h, hmem'⟩ : (nonZeroDivisors (Ideal (𝓞 E)))) = ⟨I, hmem⟩ ^ h := rfl
    rw [e1, map_pow, hh, pow_card_eq_one]
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, I ^ h = Ideal.span {a} :=
    ⟨Submodule.IsPrincipal.generator (I ^ h), (Ideal.span_singleton_generator (I ^ h)).symm⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha
    exact pow_ne_zero h hI ha
  have key : ∀ j : E →+* ℂ_[p],
      (h : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) I = Real.log ‖j (a : E)‖ := by
    intro j
    have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
      j.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)
    rw [← logIdeal_pow E p _ hinj I hI h, ha, (GlobalTheory.T.log_ideal_mul_span_map E p _ hinj).2.1]
    rfl
  have haE : (a : E) ≠ 0 := by
    intro h0
    exact ha0 (RingOfIntegers.coe_eq_zero_iff.mp h0)
  have hprod : ∏ j : E →+* ℂ_[p], j (a : E) = ((Algebra.norm ℤ a : ℤ) : ℂ_[p]) := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ_[p]) (fun j => j (a : E))
      (fun σ => σ (a : E)) (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (a : E),
      ← Algebra.coe_norm_int, map_intCast]
  have hN : ((Algebra.norm ℤ a).natAbs : ℕ) = Ideal.absNorm I ^ h := by
    rw [← Ideal.absNorm_span_singleton, ← ha, map_pow]
  have hnorm : ‖((Algebra.norm ℤ a : ℤ) : ℂ_[p])‖ = ‖((Ideal.absNorm I : ℕ) : ℂ_[p])‖ ^ h := by
    rw [← norm_pow, ← Nat.cast_pow, ← hN]
    rcases Int.natAbs_eq (Algebra.norm ℤ a) with e | e
    · conv_lhs => rw [e]
      simp
    · conv_lhs => rw [e]
      simp
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  apply mul_left_cancel₀ hh0
  rw [Finset.mul_sum]
  simp_rw [key]
  rw [← Real.log_prod (fun j _ => norm_ne_zero_iff.mpr ((map_ne_zero j).mpr haE)), ← norm_prod,
    hprod, hnorm, Real.log_pow]

end PositivityTheory.Xgf
