import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostApprox

open NumberField Formalism.HC KStar.Tree

private theorem nuQD_unit (N M l : ℕ) [Fact l.Prime] (hN : N = M * l) (hM : M ≠ 0) (hc : M.Coprime l)
    (u : ℤ_[l]ˣ) :
    ∃ v : (ZMod N)ˣ, (v : ZMod N).val ≡ 1 [MOD M] ∧
      (l : ℤ_[l]) ^ N.factorization l ∣
        ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) - ((((v ^ 2 : (ZMod N)ˣ) : ZMod N).val : ℕ) : ℤ_[l]) := by
  subst hN
  have hl : l.Prime := Fact.out
  haveI : NeZero M := ⟨hM⟩
  haveI : NeZero (M * l) := ⟨mul_ne_zero hM hl.ne_zero⟩
  let e := ZMod.chineseRemainder hc
  let w : (ZMod M × ZMod l)ˣ := MulEquiv.prodUnits.symm (1, Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u)
  let v : (ZMod (M * l))ˣ := Units.map e.symm.toRingHom.toMonoidHom w
  have he : e (v : ZMod (M * l)) = (w : ZMod M × ZMod l) := by
    simp [v]
  have hw : (w : ZMod M × ZMod l) = (1, PadicInt.toZMod (u : ℤ_[l])) := rfl
  have h1 : ZMod.cast (v : ZMod (M * l)) = (1 : ZMod M) := by
    have := congrArg Prod.fst he
    rw [hw] at this
    simpa [e, ZMod.chineseRemainder] using this
  have h2 : ZMod.cast (v : ZMod (M * l)) = PadicInt.toZMod (u : ℤ_[l]) := by
    have := congrArg Prod.snd he
    rw [hw] at this
    simpa [e, ZMod.chineseRemainder] using this
  have hfac : (M * l).factorization l = 1 := by
    rw [Nat.factorization_mul hM hl.ne_zero]
    simp only [Finsupp.add_apply, hl.factorization_self]
    have : ¬ l ∣ M := fun h => by
      have h' := Nat.Coprime.coprime_dvd_left h hc
      have h'' : l = 1 := by simpa using h'
      exact hl.one_lt.ne' h''
    rw [Nat.factorization_eq_zero_of_not_dvd this]
  refine ⟨v, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, h1, Nat.cast_one]
  · rw [hfac, pow_one]
    have hk : PadicInt.toZMod (((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) - ((((v ^ 2 : (ZMod (M * l))ˣ) : ZMod (M * l)).val : ℕ) : ℤ_[l])) = 0 := by
      rw [map_sub, map_natCast, ZMod.natCast_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        map_pow, ZMod.cast_pow (dvd_mul_left l M), h2, sub_self]
    have hmem : _ ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := hk
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    exact hmem

theorem UpperTheory.Mu.nuQD :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), (l = H.q ∨ l = H.d) → ¬ (l - 1) / 2 ∣ n → nuOf l (cyc l H.E Ω) n = 0 := by
  intro φ H l _ Ω _ _ _ n hl hn
  have hl2 : l ≠ 2 := by
    rcases hl with rfl | rfl
    · exact H.q_ne_two
    · exact H.d_ne_two
  obtain ⟨u, hu⟩ := exists_sq_unit_not_dvd l n hn hl2
  have hle := nuOf_le_of_approx l (cyc l H.E Ω) n 0 (u ^ 2) ?_ hu
  · omega
  intro k
  have hN : H.condN = H.QS * H.q * H.d := rfl
  rcases hl with rfl | rfl
  · obtain ⟨v, hv1, hv⟩ := nuQD_unit H.condN (H.QS * H.d) H.q (by rw [hN]; ring)
      (mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero) H.coprime_QSd_q u
    have ha : H.art (v ^ 2) = 1 := by
      rw [map_pow]
      exact H.art_q v hv1
    exact UpperTheory.Mu.hostApprox φ H H.q Ω (v ^ 2) ha (u ^ 2) hv k
  · obtain ⟨v, hv1, hv⟩ := nuQD_unit H.condN (H.QS * H.q) H.d hN
      (mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.coprime_QSq_d u
    have ha : H.art (v ^ 2) = 1 := by
      haveI : NeZero (H.QS * H.q) := ⟨mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero⟩
      haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
      have hdvd : H.QS * H.q ∣ H.condN := ⟨H.d, hN⟩
      have hv2 : ((v ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] := by
        have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hv1
        rw [ZMod.natCast_val] at h1
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Units.val_pow_eq_pow_val,
          ZMod.cast_pow hdvd, h1]
        simp
      have hd2 := H.art_d (v ^ 2) hv2
      rw [map_pow] at hd2 ⊢
      rcases H.art_d v hv1 with h | h
      · rw [h, one_pow]
      · rw [h] at hd2 ⊢
        rcases hd2 with h' | h'
        · exact h'
        · have hi : φ.iod = 1 := by
            rw [pow_two] at h'
            exact mul_eq_left.mp h'
          rw [hi, one_pow]
    exact UpperTheory.Mu.hostApprox φ H H.d Ω (v ^ 2) ha (u ^ 2) hv k
