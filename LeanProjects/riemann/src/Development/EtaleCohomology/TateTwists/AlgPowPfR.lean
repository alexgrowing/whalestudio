import Development.EtaleCohomology.TateTwists.TwSecLocPfZarR

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AlgPowPf

theorem root_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z : K)
    (hz : aeval z (cyclotomic q ℤ) = 0) : IsPrimitiveRoot z q := by
  have : NeZero (q : K) := ⟨hq⟩
  have h : (cyclotomic q K).IsRoot z := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    simpa [aeval_def] using hz
  exact (isRoot_cyclotomic_iff).1 h

theorem eq_pow_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (z x : K)
    (hz : IsPrimitiveRoot z q) (hx : IsPrimitiveRoot x q) : ∃ b : (ZMod q)ˣ, x = z ^ (b : ZMod q).val := by
  obtain ⟨i, hi, hzi⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hzi ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hzi]

theorem pow_ne_dom {K : Type} [CommRing K] (q : ℕ) [NeZero q] (z : K)
    (hz : IsPrimitiveRoot z q) (a b : (ZMod q)ˣ) (h : a ≠ b) :
    z ^ (a : ZMod q).val ≠ z ^ (b : ZMod q).val := by
  intro e
  apply h
  exact Units.ext (ZMod.val_injective q (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e))

theorem pow_q {A : Type} [CommRing A] (q : ℕ) (z : A) (hz : aeval z (cyclotomic q ℤ) = 0) : z ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval z) hp
  simp [hz] at this
  exact sub_eq_zero.1 this

theorem self_sq {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (x y : A)
    (hx : x ^ q = 1) (hy : y ^ q = 1) : ∃ w : A, x - y = (x - y) ^ 2 * w := by
  set d := x - y
  set u := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)
  have hdu : u * d = 0 := by
    have := geom_sum₂_mul x y q
    rw [hx, hy, sub_self] at this
    exact this
  have hyu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ (q - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q)), hy]⟩
  set c : A := (q : A) * y ^ (q - 1)
  have hc : IsUnit c := hq.mul (hyu.pow _)
  have hmem : u - c ∈ Ideal.span {d} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy : Ideal.Quotient.mk (Ideal.span {d}) x = Ideal.Quotient.mk (Ideal.span {d}) y := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl
    simp only [u, c, map_sub, map_sum, map_mul, map_pow, map_natCast, hxy]
    rw [geom_sum₂_self, sub_self]
  obtain ⟨w0, hw0⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨-(w0 * ↑cu⁻¹), ?_⟩
  have hdc : d * c = -(d ^ 2 * w0) := by
    have : c = u - w0 * d := by rw [hw0]; ring
    rw [this]; linear_combination hdu
  calc d = d * c * ↑cu⁻¹ := by rw [← hcu, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [hdc]; ring

theorem self_pow {A : Type} [CommRing A] (d w : A) (h : d = d ^ 2 * w) (k : ℕ) : d = d ^ (k + 1) * w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc d = d ^ (k + 1) * w ^ k := ih
      _ = d ^ k * d * w ^ k := by ring
      _ = d ^ k * (d ^ 2 * w) * w ^ k := by rw [← h]
      _ = _ := by ring

theorem AlgPow_of : LateralTheory.EtaleFoundations.TwSecLocPf.AlgPow := by
  classical
  intro q _ A _ ζ ξ
  obtain ⟨hqA, hζ⟩ := ζ.2
  obtain ⟨-, hξ⟩ := ξ.2
  let f : (ZMod q)ˣ → A := fun a => ∏ b ∈ Finset.univ.erase a, (ξ.1 - ζ.1 ^ (b : ZMod q).val)

  have hdom : ∀ p : Ideal A, p.IsPrime → IsPrimitiveRoot (Ideal.Quotient.mk p ζ.1) q ∧
      IsPrimitiveRoot (Ideal.Quotient.mk p ξ.1) q := by
    intro p hp
    have hq : ((q : ℕ) : A ⧸ p) ≠ 0 := by
      have := hqA.map (Ideal.Quotient.mk p)
      rw [map_natCast] at this
      exact this.ne_zero
    have hm : ∀ z : A, aeval z (cyclotomic q ℤ) = 0 → aeval (Ideal.Quotient.mk p z) (cyclotomic q ℤ) = 0 := by
      intro z hz
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ p) z (cyclotomic q ℤ)
      rw [hz, map_zero] at this
      simpa using this
    exact ⟨root_dom q hq _ (hm _ hζ), root_dom q hq _ (hm _ hξ)⟩
  refine ⟨Set.range f, ?_, ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h1, h2⟩ := hdom m hm.isPrime
    obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
    have hin : f b0 ∈ m := hsm (Ideal.subset_span ⟨b0, rfl⟩)
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hin
    simp only [f, map_prod, map_sub, map_pow, hb0] at hin
    rw [Finset.prod_eq_zero_iff] at hin
    obtain ⟨b, hb, e⟩ := hin
    exact pow_ne_dom q _ h1 b0 b (Finset.ne_of_mem_erase hb).symm (sub_eq_zero.1 e)
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    have hnil : IsNilpotent (f a * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro p hp
      have hp : p.IsPrime := hp
      obtain ⟨h1, h2⟩ := hdom p hp
      obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [f, map_mul, map_prod, map_sub, map_pow, hb0]
      by_cases hab : b0 = a
      · subst hab; simp
      · apply mul_eq_zero_of_left
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩) (sub_self _)
    obtain ⟨n, hn⟩ := hnil
    obtain ⟨w, hw⟩ := self_sq q hqA ξ.1 (ζ.1 ^ (a : ZMod q).val) (pow_q q _ hξ)
      (by rw [← pow_mul, mul_comm, pow_mul, pow_q q _ hζ, one_pow])
    refine ⟨n, ?_⟩
    rw [self_pow _ w hw n, pow_succ, mul_pow] at *
    calc f a ^ n * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n)
        = (f a ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n) * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n) := by ring
      _ = 0 := by rw [hn, zero_mul]

end LateralTheory.EtaleFoundations.AlgPowPf
