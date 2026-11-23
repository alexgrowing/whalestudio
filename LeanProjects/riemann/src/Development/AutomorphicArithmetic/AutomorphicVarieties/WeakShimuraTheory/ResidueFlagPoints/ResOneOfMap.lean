import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem eq_one_of_res {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {x : R} {m : ℕ} (hm : IsUnit (m : R))
    (h1 : residue R x = 1) (hx : x ^ m = 1) : x = 1 := by
  have hs : IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
    have h0 : residue R (∑ i ∈ Finset.range m, x ^ i) = residue R (m : R) := by
      simp [map_sum, map_pow, h1]
    by_contra hn
    have hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal R := hn
    rw [← residue_eq_zero_iff, h0] at hmem
    exact (residue_eq_zero_iff _).mp hmem hm
  have hg := geom_sum_mul x m
  rw [hx, sub_self] at hg
  exact sub_eq_zero.mp ((hs.mul_right_eq_zero).mp hg)

private theorem res_one_of_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (f : R →+* S) {x : R}
    (h : residue S (f x) = 1) : residue R x = 1 := by
  by_contra hn
  have hu : IsUnit (x - 1) := by
    by_contra hu
    exact hn (sub_eq_zero.mp (by rw [← map_one (residue R), ← map_sub]; exact (residue_eq_zero_iff _).mpr hu))
  have hfu := hu.map f
  rw [map_sub, map_one] at hfu
  have hz : residue S (f x - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
  exact ((residue_eq_zero_iff _).mp hz) hfu

private theorem not_valuation_natCast_prime_lt_one_link {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) : ¬ (K.s.A K.s.v0).valuation (l : Ω) < 1 := by
  intro hv
  have hmem : (l : 𝓞 (W.Lp T.L)) ∈ K.s.v0.asIdeal := by
    rw [← K.s.hA K.s.v0 (l : 𝓞 (W.Lp T.L))]
    simpa using hv
  have hmax := K.s.v0.isMaximal
  letI : Field (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) := Ideal.Quotient.field _
  have hcard : Nat.card (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = K.s.p := K.s.norm_v0_eq_one
  have hfin : Finite (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact K.s.p_prime.ne_zero
  letI := Fintype.ofFinite (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal)
  have hp0 : ((K.s.p : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hl0 : ((l : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have h1 := Nat.dvd_gcd (ringChar.dvd hp0) (ringChar.dvd hl0)
  rw [(Nat.coprime_primes K.s.p_prime (Fact.out)).mpr K.s.p_ne] at h1
  have h0 : ((1 : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := (ringChar.spec _ 1).mpr h1
  simp at h0

theorem UpperTheory.V.Ws.Pt.ptUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g ∈ (T.fr ∅).N, r g = 1) → ∀ g ∈ Ine (F := T.L) (K.s.A K.s.v0), K.rhoQ n r g = 1 := by
  intro Ω _ _ _ l _ c D T c' h K n r hr g hg
  have hv := not_valuation_natCast_prime_lt_one_link K
  have hβ : K.β g = 1 := K.β_t (K.t_unr _ hv hg)
  obtain ⟨m, hcop, hm⟩ := K.tame
  have hchib : ∀ i, (K.r.chib i) (K.V.pr g) = 1 := fun i => K.v0.1 i (Subgroup.mem_map_of_mem K.V.pr hg)
  have hres : ∀ i, residue c'.O ((K.κ g : c'.O) * inc h ((chi D T.pr i) (resQ T.L g) : c.O)) = 1 := by
    intro i
    rw [← K.chib i g, hchib i, Units.val_one]
  have hi3 : ∃ i, lab T.pr i = 3 := by
    unfold lab
    split
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
  have hsurj : ∀ j, ∃ i, lab T.pr i = j := by
    unfold lab
    split
    · decide
    · intro j
      exact ⟨j, rfl⟩
  obtain ⟨i3, hi3⟩ := hi3
  have hκr : residue c'.O (K.κ g : c'.O) = 1 := by
    have h3 := hres i3
    have hc : (chi D T.pr i3) (resQ T.L g) = 1 := by
      simp [chi, hi3, Raw.ps]
    rw [hc, Units.val_one, map_one, mul_one] at h3
    exact h3
  have hκ : K.κ g = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply eq_one_of_res ((dvrFacts l c'.O).2.2.2.2.2.2.2.2 m ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)) hκr
    rw [← Units.val_pow_eq_pow_val, hm _ hv g hg, Units.val_one]
  have hps : ∀ j, residue c.O ((D.ps j) (resQ T.L g) : c.O) = 1 := by
    intro j
    obtain ⟨i, hi⟩ := hsurj j
    apply res_one_of_map (inc h)
    have h4 := hres i
    rw [map_mul, hκr, one_mul] at h4
    rw [← hi]
    exact h4
  have hrbar : D.rbar (resQ T.L g) = 1 := by
    unfold Raw.rbar Raw.r0
    ext a b
    simp only [GradeZeroInterpolatingElement.mapRep, GradeZeroInterpolatingElement.diagRep, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      show ((residue c.O).mapMatrix _) a a = 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact hps a
    · show ((residue c.O).mapMatrix _) a b = 0
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hab, map_zero]
  have hN : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨K.s.A K.s.v0, ?_, (resLe_mem_Ine T.F_le).mpr hg, hrbar⟩
    intro q hq
    have hq' : q = l := by simpa using hq
    subst hq'
    exact hv
  apply Units.ext
  rw [Link.rho_val, hr _ hN, Units.val_one]
  have htw : ((K.twc n) g : PadicAlgCl l) = 1 := by
    rw [Link.twc_val, hκ, hβ]
    simp
  rw [htw, one_smul]
