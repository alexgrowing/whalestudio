import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocSplitOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfA

theorem pow_q_eq_one {q : ℕ} {B : Type} [CommRing B] (x : B)
    (hx : Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0) : x ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (Polynomial.aeval x) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hx, zero_mul] at this
  exact sub_eq_zero.1 this

theorem local_eq {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {x y : B}
    (hx : x ^ q = 1) (hy : y ^ q = 1) (hr : IsLocalRing.residue B x = IsLocalRing.residue B y) : x = y := by
  have hg := geom_sum₂_mul x y q
  rw [hx, hy, sub_self] at hg
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy (NeZero.ne q)
  have hres : IsLocalRing.residue B (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) =
      IsLocalRing.residue B ((q : B) * y ^ (q - 1)) := by
    rw [map_sum, map_mul, map_pow, map_natCast]
    rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue B y ^ (q - 1))]
    · simp
    · intro i hi
      rw [map_mul, map_pow, map_pow, hr, ← pow_add]
      congr 1; have := Finset.mem_range.1 hi; omega
  have hu' : IsUnit (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) := by
    have h1 : IsUnit (IsLocalRing.residue B ((q : B) * y ^ (q - 1))) := (hq.mul (hyu.pow _)).map _
    rw [← hres] at h1
    exact (isUnit_map_iff (IsLocalRing.residue B) _).1 h1
  exact sub_eq_zero.1 ((IsUnit.mul_right_eq_zero hu').1 hg)

theorem res_root {q : ℕ} {B : Type} [CommRing B] [IsLocalRing B] (z : B)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) :
    Polynomial.IsRoot (Polynomial.cyclotomic q (IsLocalRing.ResidueField B)) (IsLocalRing.residue B z) := by
  have h := Polynomial.aeval_algHom_apply (IsLocalRing.residue B).toIntAlgHom z (Polynomial.cyclotomic q ℤ)
  rw [hz, map_zero] at h
  rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem local_pow {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {ζ ξ : B}
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = ζ ^ (a : ZMod q).val := by
  have : NeZero ((q : ℕ) : IsLocalRing.ResidueField B) :=
    ⟨by simpa [map_natCast] using (hq.map (IsLocalRing.residue B)).ne_zero⟩
  have root : ∀ z : B, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
      IsPrimitiveRoot (IsLocalRing.residue B z) q := fun z hz =>
    Polynomial.isRoot_cyclotomic_iff.1 (res_root z hz)
  obtain ⟨i, hi, hpow⟩ := (root ζ hζ).eq_pow_of_pow_eq_one ((root ξ hξ).pow_eq_one)
  have hc : i.Coprime q :=
    ((root ζ hζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hpow ▸ root ξ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine local_eq hq (pow_q_eq_one ξ hξ) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_q_eq_one ζ hζ, one_pow]
  · rw [map_pow]; exact hpow.symm

end LateralTheory.E.LeafTw0LocGenPfA
