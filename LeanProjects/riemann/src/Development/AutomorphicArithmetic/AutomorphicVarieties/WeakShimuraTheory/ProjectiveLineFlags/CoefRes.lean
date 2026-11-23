import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.P1.coefRes {l : ℕ} [hl : Fact l.Prime] (c : Coef l) :
    Finite (ResidueField c.O) ∧ CharP (ResidueField c.O) l ∧
      (∀ (c' : Coef l) (h : c.O ≤ c'.O), IsLocalHom (inc h)) ∧
      ∀ (m : ℕ) (x : c.O), l.Coprime m → x ^ m = 1 → residue c.O x = 1 → x = 1 := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, hfin, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hchar : CharP (ResidueField c.O) l := by
    obtain ⟨p, hp⟩ := CharP.exists (ResidueField c.O)
    have hp0 := CharP.char_ne_zero_of_finite (ResidueField c.O) p
    haveI : NeZero p := ⟨hp0⟩
    have hpp := (CharP.char_is_prime_of_pos (ResidueField c.O) p).out
    have hl0 : ((l : ℕ) : ResidueField c.O) = 0 := by
      rw [← map_natCast (residue c.O)]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hlm
    have hdvd : p ∣ l := (CharP.cast_eq_zero_iff (ResidueField c.O) p l).1 hl0
    have hpl : p = l := (Nat.prime_dvd_prime_iff_eq hpp hl.out).1 hdvd
    subst hpl
    exact hp
  refine ⟨hfin, hchar, ?_, ?_⟩
  · intro c' h
    haveI := c'.fin
    have hint : (inc h).IsIntegral := by
      intro y
      obtain ⟨p, hp, hpy⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y
      refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O :=
        RingHom.ext fun a => (Subalgebra.inclusion h).commutes a
      rw [hcomp]
      exact hpy
    exact hint.isLocalHom (Subalgebra.inclusion_injective h)
  · intro m x hcop hxm hres
    have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop
    have hsum : IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
      by_contra hnu
      have hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal c.O :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
      rw [map_sum] at h0
      simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one] at h0
      exact hnd ((CharP.cast_eq_zero_iff (ResidueField c.O) l m).1 h0)
    have hg := geom_sum_mul x m
    rw [hxm, sub_self] at hg
    have hx1 : x - 1 = 0 := by
      rcases mul_eq_zero.1 hg with h | h
      · exact absurd (h ▸ hsum) not_isUnit_zero
      · exact h
    exact sub_eq_zero.1 hx1
