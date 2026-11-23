import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.CompletionAut

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_natCast_valued_lt_one :
    ∃ p : ℕ, (p : v.adicCompletion F) ≠ 0 ∧ Valued.v (p : v.adicCompletion F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, ?_⟩
  · haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · have h := Ideal.absNorm_mem v.asIdeal
    have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F)
          (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) := by simp
    rw [h2]
    erw [valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem v _).2 h

theorem exists_pow_eq_of_mem {p : ℕ} (hp : Valued.v (p : v.adicCompletion F) < 1) (e : ℕ)
    {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ y : v.adicCompletion F, y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1) := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set R := v.adicCompletionIntegers F
  have hpm : (p : R) ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have h' : Valued.v (p : v.adicCompletion F) = 1 := by simpa using h
    exact hp.ne h'
  let c : R := 1 + p * (⟨x, hx⟩ : R) ^ (p * e + 1)
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ (p * e + 1) - C c) (monic_X_pow_sub_C c (Nat.succ_ne_zero _)) 1
    (by
      simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow, c]
      have : (1 : R) - (1 + p * (⟨x, hx⟩ : R) ^ (p * e + 1)) =
          p * (-(⟨x, hx⟩ : R) ^ (p * e + 1)) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hpm)
    (by
      have h0 : Ideal.Quotient.mk (maximalIdeal R) (p : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hpm
      rw [map_natCast] at h0
      simp [derivative_X_pow, h0])
  refine ⟨a, ?_⟩
  have h1 : a ^ (p * e + 1) = c := by
    simpa [IsRoot, sub_eq_zero] using ha
  have := congrArg (fun z : R => (z : v.adicCompletion F)) h1
  simpa [c] using this

theorem mem_of_pow_eq {p e : ℕ} (he : 0 < e)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-(e : ℤ))) (hp0 : p ≠ 0)
    {x y : v.adicCompletion F} (h : y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1)) :
    x ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers]
  by_contra hx
  push Not at hx
  have hx0 : Valued.v x ≠ 0 := (zero_lt_one.trans hx).ne'
  set l := p * e + 1 with hl
  have hle : e < l := by
    have : e ≤ p * e := Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero hp0)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hm0 : 0 < m := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx; exact hx
  have h1 : Valued.v ((p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [map_mul, map_pow, hp, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
  have hpos : 0 < -(e : ℤ) + l * m := by
    have : (e : ℤ) < l := by exact_mod_cast hle
    nlinarith
  have h2 : Valued.v (1 + (p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [← h1]
    apply Valuation.map_add_eq_of_lt_right
    rw [h1, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact hpos
  rw [← h, map_pow] at h2
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h2
    exact WithZero.exp_ne_zero h2.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v y = WithZero.exp k := ⟨_, (WithZero.exp_log hy0).symm⟩
  rw [hk, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  have hd : (l : ℤ) ∣ (e : ℤ) := ⟨m - k, by linear_combination h2⟩
  have := Nat.le_of_dvd he (Int.natCast_dvd_natCast.1 hd)
  omega

theorem map_mem (θ : v.adicCompletion F →+* v.adicCompletion F) {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) : θ x ∈ v.adicCompletionIntegers F := by
  obtain ⟨p, hp0, hp⟩ := exists_natCast_valued_lt_one v
  have hv0 : Valued.v (p : v.adicCompletion F) ≠ 0 := by simpa using hp0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (p : v.adicCompletion F) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  have hm0 : m < 0 := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hp; exact hp
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m by omega)
  obtain ⟨y, hy⟩ := exists_pow_eq_of_mem v hp e hx
  refine mem_of_pow_eq v (p := p) (e := e) (y := θ y) (by omega) (by rw [hm, ← he, neg_neg])
    (by rintro rfl; simp at hp0) ?_
  simpa using congrArg θ hy

end GlobalTheory.CompletionAut

namespace GlobalTheory

theorem ringEquiv_adicCompletion_mem_integers_iff (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (θ : v.adicCompletion F ≃+* v.adicCompletion F)
    (x : v.adicCompletion F) :
    θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F :=
  ⟨fun h => by simpa using CompletionAut.map_mem v θ.symm.toRingHom h,
    fun h => CompletionAut.map_mem v θ.toRingHom h⟩

end GlobalTheory
