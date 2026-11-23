import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem UpperTheory.V.X.xiSq_ft {R : Type} [CommRing R] {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n)
    (hd : d ∣ n) : χ.FactorsThrough d ↔ ∀ a : ℤ, IsCoprime a n → (d : ℤ) ∣ a - 1 → χ a = 1 := by
  constructor
  · rintro ⟨hd', χ₀, rfl⟩ a ha hda
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd' ha]
    have : ((a : ℤ) : ZMod d) = 1 := by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mpr hda
      push_cast at h0
      exact sub_eq_zero.mp h0
    rw [this, map_one]
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    set a : ℤ := ((x : ZMod n).val : ℤ) with ha_def
    have hax : ((a : ℤ) : ZMod n) = (x : ZMod n) := by
      simp [ha_def, ZMod.natCast_zmod_val]
    have hcop : IsCoprime a n := by
      have hu : IsUnit ((a : ℤ) : ZMod n) := by rw [hax]; exact x.isUnit
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
      exact hu.symm
    have hd1 : (d : ℤ) ∣ a - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mp
      have h1 := congrArg (fun u : (ZMod d)ˣ => (u : ZMod d)) hx
      simp only [ZMod.unitsMap_val, Units.val_one] at h1
      rw [ZMod.cast_eq_val] at h1
      push_cast
      rw [ha_def]
      push_cast
      rw [h1, sub_self]
    have := h a hcop hd1
    rw [hax] at this
    ext
    simpa using this

private theorem UpperTheory.V.X.xiSq_cong {R : Type} [CommRing R] {n : ℕ} (χ : DirichletCharacter R n)
    {a b : ℤ} (h : (n : ℤ) ∣ a - b) : χ a = χ b := by
  congr 1
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp h)

private theorem UpperTheory.V.X.xiSq_cop (t : ℤ) (m : ℕ) : IsCoprime (1 + 2 * t) ((2 ^ m : ℕ) : ℤ) := by
  push_cast
  exact IsCoprime.pow_right ⟨1, -t, by ring⟩

private theorem UpperTheory.V.X.exists_primitive_square_twist {O : Type} [CommRing O] (k : ℕ) (ψ : DirichletCharacter O (2 ^ (k + 4)))
    (hψ : ψ.IsPrimitive) : ∃ ξ : DirichletCharacter O (2 ^ (k + 3)), ξ.IsPrimitive ∧
      ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  have h4 : 4 ∣ 2 ^ (k + 4) := Dvd.intro (2 ^ k * 4) (by ring)
  let χ4O : DirichletCharacter O 4 := ZMod.χ₄.ringHomComp (Int.castRingHom O)
  let φ : DirichletCharacter O (2 ^ (k + 4)) := ψ ^ 2 * DirichletCharacter.changeLevel h4 χ4O
  have hsq : ∀ a : ℤ, ψ a ^ 2 = ψ ((a ^ 2 : ℤ) : ZMod (2 ^ (k + 4))) := by
    intro a
    rw [Int.cast_pow, map_pow]
  have h1 : ψ ((1 : ℤ) : ZMod (2 ^ (k + 4))) = 1 := by rw [Int.cast_one, map_one]
  have hc4 : ∀ a : ℤ, (4 : ℤ) ∣ a - 1 → ((ZMod.χ₄ a : ℤ) : O) = 1 := by
    intro a ha
    have := UpperTheory.V.X.xiSq_cong ZMod.χ₄ (n := 4) (a := a) (b := 1) (by exact_mod_cast ha)
    rw [this]
    simp
  have hval : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) →
      φ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    simp only [φ, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.pow_apply' _ two_ne_zero]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ h4 ha]
    simp [χ4O, MulChar.ringHomComp_apply]
  have hd : 2 ^ (k + 3) ∣ 2 ^ (k + 4) := pow_dvd_pow 2 (by omega)
  have hft : φ.FactorsThrough (2 ^ (k + 3)) := by
    rw [UpperTheory.V.X.xiSq_ft φ hd]
    intro a ha hda
    rw [hval a ha]
    obtain ⟨t, ht⟩ := hda
    push_cast at ht
    have ha' : a = 1 + 2 ^ (k + 3) * t := by linarith
    rw [hc4 a ⟨2 ^ (k + 1) * t, by rw [ha']; ring⟩, mul_one, hsq]
    rw [UpperTheory.V.X.xiSq_cong ψ (a := a ^ 2) (b := 1) ⟨t + 2 ^ (k + 2) * t ^ 2, by push_cast; rw [ha']; ring⟩]
    exact h1
  obtain ⟨hd', ξ, hξ⟩ := hft
  have hξv : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    rw [← DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ hd' ha, ← hξ, hval a ha]
  refine ⟨ξ, ?_, hξv⟩
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ξ.conductor_dvd_level
  show ξ.conductor = 2 ^ (k + 3)
  rw [hj']
  rcases Nat.lt_or_ge j (k + 3) with hlt | hge
  · exfalso
    have hf : ξ.FactorsThrough (2 ^ (k + 2)) :=
      DirichletCharacter.FactorsThrough.mono ξ ξ.factorsThrough_conductor
        (by rw [hj']; exact pow_dvd_pow 2 (by omega)) (pow_dvd_pow 2 (by omega))
    rw [UpperTheory.V.X.xiSq_ft ξ (pow_dvd_pow 2 (by omega))] at hf
    set b : ℤ := 1 + 2 * 2 ^ (k + 1) with hb
    have hb3 := hf b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 3))
      ⟨1, by push_cast; rw [hb]; ring⟩
    rw [hξv b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 4)),
      hc4 b ⟨2 ^ k, by rw [hb]; ring⟩, mul_one, hsq,
      UpperTheory.V.X.xiSq_cong ψ (a := b ^ 2) (b := 1 + 2 ^ (k + 3)) ⟨2 ^ k, by push_cast; rw [hb]; ring⟩] at hb3
    have hψf : ψ.FactorsThrough (2 ^ (k + 3)) := by
      rw [UpperTheory.V.X.xiSq_ft ψ hd]
      intro a ha hda
      obtain ⟨t, ht⟩ := hda
      push_cast at ht
      obtain ⟨s, hs | hs⟩ := Int.even_or_odd' t
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact h1
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1 + 2 ^ (k + 3)) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact hb3
    have hle : ψ.conductor ≤ 2 ^ (k + 3) := Nat.sInf_le hψf
    have hpr : ψ.conductor = 2 ^ (k + 4) := hψ
    rw [hpr] at hle
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (show k + 3 < k + 4 by omega)
    omega
  · congr 1
    omega

theorem UpperTheory.V.X.xiSq :
    ∀ (O : Type) [CommRing O] [IsDomain O], (2 : O) ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (c : ℕ), 4 ≤ c → χ.conductor = 2 ^ c → ∃ ξ : DirichletCharacter O (2 ^ (c - 1)), ξ.IsPrimitive ∧ ∀ a : ℤ, IsCoprime a N → ξ a = χ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  intro O _ _ _ N _ χ c hc hcond
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
  have hf : χ.FactorsThrough (2 ^ (k + 4)) := hcond ▸ χ.factorsThrough_conductor
  obtain ⟨hdv, ψ, hψχ⟩ := hf
  have hψp : ψ.IsPrimitive := by
    show ψ.conductor = 2 ^ (k + 4)
    have h := DirichletCharacter.conductor_changeLevel ψ hdv
    rw [← hψχ, hcond] at h
    exact h.symm
  obtain ⟨ξ, hp, hv⟩ := UpperTheory.V.X.exists_primitive_square_twist k ψ hψp
  refine ⟨ξ, hp, fun a ha => ?_⟩
  have ha' : IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) :=
    ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hdv)
  rw [hv a ha', hψχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdv ha]
