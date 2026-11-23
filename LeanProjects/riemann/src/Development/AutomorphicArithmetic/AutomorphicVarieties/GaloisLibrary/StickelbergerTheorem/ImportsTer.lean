import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.teich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M d : ℕ) (ζ : R),
    IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M → M * d = p - 1 →
    ∃ χ : MulChar (ZMod p) R, (∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d) ∧ orderOf χ = M := by
  intro R _ _ p hp π M d ζ hζ hv hMd
  have hpp : p.Prime := hp.out
  have hM : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hMd
    have := hpp.two_le
    omega
  have hd : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hMd
    have := hpp.two_le
    omega
  haveI : NeZero M := ⟨hM⟩
  have U : ∀ r s : R, r ^ M = 1 → s ^ M = 1 → π r = π s → r = s := by
    intro r s hr hs h
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hr
    obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hs
    rw [map_pow, map_pow] at h
    rw [hv.pow_inj hi hj h]
  have E : ∀ y : ZMod p, y ^ M = 1 → ∃ r : R, r ^ M = 1 ∧ π r = y := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := hv.eq_pow_of_pow_eq_one hy
    refine ⟨ζ ^ i, ?_, by rw [map_pow]⟩
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have P : ∀ x : ZMod p, x ≠ 0 → (x ^ d) ^ M = 1 := by
    intro x hx
    rw [← pow_mul, mul_comm, hMd]
    exact ZMod.pow_card_sub_one_eq_one hx
  classical
  let L : ZMod p → R := fun x => if h : x = 0 then 0 else (E _ (P x h)).choose
  have L1 : ∀ x (h : x ≠ 0), L x ^ M = 1 ∧ π (L x) = x ^ d := by
    intro x h
    simp only [L, dif_neg h]
    exact (E _ (P x h)).choose_spec
  have L0 : L 0 = 0 := by simp [L]
  let χ : MulChar (ZMod p) R :=
    { toFun := L
      map_one' := by
        have h1 := L1 1 one_ne_zero
        exact U _ _ h1.1 (one_pow M) (by rw [h1.2, one_pow, map_one])
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, L0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, L0, mul_zero]
        have hxy := L1 (x * y) (mul_ne_zero hx hy)
        have h1 := L1 x hx
        have h2 := L1 y hy
        refine U _ _ hxy.1 (by rw [mul_pow, h1.1, h2.1, one_mul]) ?_
        rw [hxy.2, map_mul, h1.2, h2.2, mul_pow]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (isUnit_iff_ne_zero.mpr h)
        rw [this]
        exact L0 }
  have hχ : ∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d := L1
  refine ⟨χ, hχ, ?_⟩
  have hpow : χ ^ M = 1 := by
    ext a
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    exact (hχ a a.ne_zero).1
  have hdvd : orderOf χ ∣ M := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  set k := orderOf χ with hk
  have hk1 : χ ^ k = 1 := pow_orderOf_eq_one χ
  have hgk : (χ g) ^ k = 1 := by
    rw [← MulChar.pow_apply_coe, hk1, MulChar.one_apply_coe]
  have hgdk : g ^ (d * k) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← (hχ g g.ne_zero).2, ← map_pow, hgk,
      map_one]
  have h2 : M * d ∣ d * k := by
    rw [hMd, ← hog]
    exact orderOf_dvd_of_pow_eq_one hgdk
  rw [mul_comm M d] at h2
  have h3 : M ∣ k := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)).mp h2
  exact Nat.dvd_antisymm hdvd h3
