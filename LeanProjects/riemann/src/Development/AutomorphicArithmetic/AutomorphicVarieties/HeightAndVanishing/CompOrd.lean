import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem co_proj_eq_one {N : ℕ} (r : ℕ) (hr : r.Prime) (u : (ZMod N)ˣ)
    (h : ((ordProj[r] N : ℕ) : ZMod N) ∣ (u : ZMod N) - 1) : proj r N u = 1 := by
  obtain ⟨t, ht⟩ := h
  have hpos : 0 < Nat.totient (ordProj[r] N) := by
    rw [Nat.totient_pos]
    exact pow_pos hr.pos _
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h0 : idem r N * ((ordProj[r] N : ℕ) : ZMod N) = 0 := by
    unfold idem
    rw [hk, ← Nat.cast_mul, pow_succ, mul_assoc, mul_comm (ordCompl[r] N),
      Nat.ordProj_mul_ordCompl_eq_self, Nat.cast_mul, ZMod.natCast_self, mul_zero]
  ext
  change idem r N * (u : ZMod N) + (1 - idem r N) = 1
  linear_combination idem r N * ht + t * h0

private theorem co_dvd_of_unitsMap {N d : ℕ} [NeZero N] (hd : d ∣ N) (u : (ZMod N)ˣ)
    (h : ZMod.unitsMap hd u = 1) : ((d : ℕ) : ZMod N) ∣ (u : ZMod N) - 1 := by
  rw [Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
  obtain ⟨t, ht⟩ := h.symm.dvd
  refine ⟨(t : ZMod N), ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod N) ht
  simpa using this

private theorem co_toUnitHom {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  simp [comp]

private theorem co_pow_toUnitHom {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (u : (ZMod N)ˣ) :
    (χ ^ k).toUnitHom u = χ.toUnitHom u ^ k := by
  ext
  simp [MulChar.pow_apply_coe]

private theorem co_pow_eq_one_iff {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) :
    χ ^ k = 1 ↔ ∀ u, χ.toUnitHom u ^ k = 1 := by
  simp_rw [← co_pow_toUnitHom]
  constructor
  · intro h u
    rw [h]
    ext
    simp
  · intro h
    ext u
    simpa using congrArg Units.val (h u)

private theorem co_ord_dvd {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) : orderOf (comp r χ) ∣ Nat.totient (ordProj[r] N) := by
  rw [orderOf_dvd_iff_pow_eq_one, co_pow_eq_one_iff]
  intro u
  have : NeZero (ordProj[r] N) := ⟨(pow_pos hr.pos _).ne'⟩
  rw [← map_pow, co_toUnitHom, co_proj_eq_one r hr, map_one]
  apply co_dvd_of_unitsMap (Nat.ordProj_dvd N r)
  rw [map_pow, ZMod.pow_totient]

private theorem co_tame {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) (h : ¬ r ∣ orderOf (comp r χ)) :
    orderOf (comp r χ) ∣ r - 1 ∧ (comp r χ).conductor ∣ r := by
  have hc : (orderOf (comp r χ)).Coprime r := ((Nat.Prime.coprime_iff_not_dvd hr).2 h).symm
  have h1 := co_ord_dvd χ r hr
  by_cases hN : r ∣ N
  · have hpos : 0 < N.factorization r := hr.factorization_pos_of_dvd (NeZero.ne N) hN
    rw [Nat.totient_prime_pow hr hpos] at h1
    refine ⟨(hc.pow_right _).dvd_of_dvd_mul_left h1, ?_⟩
    apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.factorsThrough_iff_ker_unitsMap hN]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h2 := dvd_sub_pow_of_dvd_sub (co_dvd_of_unitsMap hN u hu) (N.factorization r)
    have h3 : (comp r χ).toUnitHom u ^ (r ^ N.factorization r) = 1 := by
      rw [← map_pow, co_toUnitHom, co_proj_eq_one r hr, map_one]
      rw [one_pow] at h2
      refine dvd_trans ?_ (by simpa using h2)
      rw [Nat.cast_pow]
      exact pow_dvd_pow _ (Nat.le_succ _)
    have h4 := (co_pow_eq_one_iff (comp r χ) _).1 (pow_orderOf_eq_one _) u
    have h5 := pow_gcd_eq_one.2 ⟨h4, h3⟩
    rwa [hc.pow_right _, pow_one] at h5
  · rw [Nat.factorization_eq_zero_of_not_dvd hN, pow_zero, Nat.totient_one, Nat.dvd_one] at h1
    refine ⟨by rw [h1]; exact one_dvd _, ?_⟩
    rw [orderOf_eq_one_iff] at h1
    rw [h1, DirichletCharacter.conductor_one]
    exact one_dvd _

theorem UpperTheory.V.HV.compOrd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (r : ℕ), r.Prime →
      orderOf (comp r χ) ∣ Nat.totient (ordProj[r] N) ∧ (∃ k, orderOf (comp 2 χ) = 2 ^ k) ∧
      (¬ r ∣ orderOf (comp r χ) → orderOf (comp r χ) ∣ r - 1 ∧ (comp r χ).conductor ∣ r) ∧
      ∀ l s : ℕ, l.Prime → l ≠ r → χ ^ l ^ s = 1 → comp r χ ≠ 1 → r ≡ 1 [MOD l] ∧ (comp r χ).conductor = r := by
  intro O _ _ N _ χ r hr
  refine ⟨co_ord_dvd χ r hr, ?_, co_tame χ r hr, ?_⟩
  · have h1 := co_ord_dvd χ 2 Nat.prime_two
    have h2 : Nat.totient (ordProj[2] N) ∣ 2 ^ (N.factorization 2 - 1) := by
      rcases Nat.eq_zero_or_pos (N.factorization 2) with h | h
      · simp [h]
      · rw [Nat.totient_prime_pow Nat.prime_two h]; simp
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h1.trans h2)
    exact ⟨k, hk⟩
  · intro l s hl hlr hχ hne
    have h1 : orderOf (comp r χ) ∣ l ^ s := by
      rw [orderOf_dvd_iff_pow_eq_one, co_pow_eq_one_iff]
      intro u
      rw [co_toUnitHom]
      exact (co_pow_eq_one_iff χ _).1 hχ _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).1 h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.1 (by simpa using hk))
    have h2 : ¬ r ∣ orderOf (comp r χ) := by
      rw [hk]
      intro h
      exact hlr ((Nat.prime_dvd_prime_iff_eq hr hl).1 (hr.dvd_of_dvd_pow h)).symm
    obtain ⟨h3, h4⟩ := co_tame χ r hr h2
    refine ⟨?_, ?_⟩
    · rw [hk] at h3
      exact ((Nat.modEq_iff_dvd' hr.one_le).2 ((dvd_pow_self l hk0).trans h3)).symm
    · rcases (Nat.dvd_prime hr).1 h4 with h | h
      · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hne
      · exact h
