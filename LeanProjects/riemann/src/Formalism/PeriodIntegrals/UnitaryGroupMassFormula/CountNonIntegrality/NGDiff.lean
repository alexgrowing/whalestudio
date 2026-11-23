import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.FrIntGOfDelta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.ValOneOfNotMem

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

variable {D : Formalism.BasicNotions.D7}

theorem ell_mem (p : PlF D) : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  unfold Loc.resChar
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem vle_iff (p : PlF D) (x y : D.host.F) :
    valuation (D.s.atP p).Fp ((D.s.atP p).ιF x) ≤ valuation (D.s.atP p).Fp ((D.s.atP p).ιF y) ↔
      p.valuation D.host.F x ≤ p.valuation D.host.F y := by
  rw [← (D.s.atP p).val x y]
  exact (Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).symm

theorem val_one_of_notMem (p : PlF D) (d : 𝓞 D.host.F) (hd : d ∉ p.asIdeal) :
    valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F d)) = 1 := by
  have h1 : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F d) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h1' : p.valuation D.host.F 1 = 1 := map_one _
  apply le_antisymm
  · have h2 := (vle_iff p (algebraMap (𝓞 D.host.F) D.host.F d) 1).2 (by rw [h1, h1'])
    simpa only [map_one] using h2
  · have h2 := (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F d)).2 (by rw [h1, h1'])
    simpa only [map_one] using h2

theorem ell_not_mem_sq (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2 := by
  intro hmem
  obtain ⟨π, hπ⟩ := p.intValuation_exists_uniformizer
  have hx1 : ¬ (p.valuation D.host.F 1 ≤ p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F π)) := by
    rw [map_one, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    norm_num
  have hxlt : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) < 1 := by
    have h1 := mt (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F π)).1 hx1
    simp only [map_one] at h1
    exact not_le.1 h1
  have hvl : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F ((Loc.resChar p : ℕ) : 𝓞 D.host.F)) ≤
      p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (π ^ 2)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_pow, hπ, ← WithZero.exp_nsmul]
    have h2 := (p.intValuation_le_pow_iff_mem _ 2).2 hmem
    convert h2 using 2 <;> norm_num
  have hq : valuation (D.s.atP p).Fp (sg.q : (D.s.atP p).Fp) ≤
      valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2 := by
    have h1 := (vle_iff p _ _).2 hvl
    simp only [map_natCast, map_pow] at h1
    rw [sg.q_eq]
    exact h1
  have hxmem : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) ∈ 𝒪[(D.s.atP p).Fp] :=
    (Valuation.mem_integer_iff _ _).2 hxlt.le
  have hI := Valuation.integer.integers (valuation (D.s.atP p).Fp)
  have hdvd : (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) ^ 2 ∣ sg.q := by
    apply hI.dvd_of_le
    change valuation _ (sg.q : (D.s.atP p).Fp) ≤
      valuation _ (((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2)
    rw [map_pow]
    exact hq
  obtain ⟨c, hc⟩ := hdvd
  have hsplit : sg.q = (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * ((⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * c) := by
    rw [hc]
    ring
  rcases sg.q_irr.isUnit_or_isUnit hsplit with hu | hu
  · have h1 := hI.isUnit_iff_valuation_eq_one.1 hu
    exact (ne_of_lt hxlt) h1
  · have h1 := hI.isUnit_iff_valuation_eq_one.1 hu
    have h2 : valuation (D.s.atP p).Fp
        ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) * (c : (D.s.atP p).Fp)) = 1 := h1
    rw [map_mul] at h2
    have hc1 : valuation (D.s.atP p).Fp (c : (D.s.atP p).Fp) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
    have h5 := mul_le_of_le_one_right'
      (a := valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π))) hc1
    rw [h2] at h5
    exact absurd hxlt (not_lt.2 h5)

theorem not_dvd_diff (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    ¬ p.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  haveI hℓ : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  have hmem := ell_mem p
  have hsq := ell_not_mem_sq p sg
  have hle : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 hmem
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  haveI hPm : p.asIdeal.IsMaximal := p.isMaximal
  have hcop : IsCoprime p.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have h1 : p.asIdeal = p.asIdeal ⊔ Q := Ideal.IsMaximal.eq_of_le hPm hne le_sup_left
    have h2 : Q ≤ p.asIdeal := by
      rw [h1]
      exact le_sup_right
    apply hsq
    have h3 : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal ^ 2 := by
      rw [hQ, sq]
      exact Ideal.mul_mono_right h2
    exact (Ideal.span_singleton_le_iff_mem _).1 h3
  have hmap : p.asIdeal * Q =
      Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, ← hQ]
  haveI : (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hℓ.out).irreducible
  haveI : NeZero (Loc.resChar p) := ⟨hℓ.out.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (Loc.resChar p)).symm.toEquiv
  exact not_dvd_differentIdeal_of_isCoprime ℤ (p := Ideal.span {((Loc.resChar p : ℕ) : ℤ)})
    p.asIdeal Q hcop hmap

theorem different_lattice_index : DiffG := by
  intro D p hs t ht
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hs
  have hnd := not_dvd_diff (D := D) p sg
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨d, hdD, hdp⟩ := SetLike.not_le_iff_exists.1 hnd
  have hdt : ∃ b : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) D.host.F b = algebraMap (𝓞 D.host.F) D.host.F d * t := by
    have h1 : algebraMap (𝓞 D.host.F) D.host.F d ∈
        (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F)) := by
      rw [← coeSubmodule_differentIdeal ℤ ℚ (𝓞 D.host.F)]
      exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hdD, rfl⟩
    have h2 : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
      obtain ⟨n, hn⟩ := ht b
      rw [Algebra.traceForm_apply]
      exact RingHom.mem_range.2 ⟨n, by simpa using hn.symm⟩
    have h3 := (Submodule.mem_div_iff_forall_mul_mem.1 h1) t h2
    exact Submodule.mem_one.1 h3
  obtain ⟨b, hb⟩ := hdt
  have hv := val_one_of_notMem (D := D) p d hdp
  have hb1 : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F b)) ≤ 1 := by
    have h4 := (vle_iff (D := D) p (algebraMap (𝓞 D.host.F) D.host.F b) 1).2
      (by rw [map_one]; exact p.valuation_le_one b)
    simpa only [map_one] using h4
  rw [hb, map_mul, map_mul, hv, one_mul] at hb1
  exact (Valuation.mem_integer_iff _ _).2 hb1

end PI.CntNotIntW
