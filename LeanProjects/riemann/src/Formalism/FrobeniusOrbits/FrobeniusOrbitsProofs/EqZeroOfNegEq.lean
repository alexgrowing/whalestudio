import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois

open NumberField IntermediateField Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Cond

section Gauss

variable {K : Type*} [Field K] [CharZero K]

def chi (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] : MulChar (ZMod p) K :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)

def gs (p : ℕ) [Fact p.Prime] {x : K} (hx : x ^ p = 1) : K :=
  gaussSum (chi p K) (AddChar.zmodChar p hx)

theorem ringChar_ne_two {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  intro h
  omega

theorem chi_neg_one {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) : chi p K (-1) = -1 := by
  have h := quadraticChar_neg_one (ringChar_ne_two hp4)
  simp only [chi, MulChar.ringHomComp_apply, h, ZMod.card]
  rw [ZMod.χ₄_nat_three_mod_four hp4]
  simp

theorem gs_sq {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : IsPrimitiveRoot x p) :
    gs p hx.pow_eq_one ^ 2 = -(p : K) := by
  have h1 : chi p K ≠ 1 := by
    intro h
    have h0 := chi_neg_one (K := K) hp4
    have h2 : (1 : MulChar (ZMod p) K) (-1) = 1 := by
      exact MulChar.one_apply isUnit_one.neg
    rw [h, h2] at h0
    norm_num at h0
  have h2 : (chi p K).IsQuadratic := by
    exact (quadraticChar_isQuadratic (ZMod p)).comp _
  have h3 : (AddChar.zmodChar p hx.pow_eq_one).IsPrimitive := by
    exact AddChar.zmodChar_primitive_of_primitive_root p hx
  unfold gs
  rw [gaussSum_sq h1 h2 h3, chi_neg_one (K := K) hp4, ZMod.card]
  ring

theorem gs_ne_zero {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : IsPrimitiveRoot x p) :
    gs p hx.pow_eq_one ≠ 0 := by
  intro h
  have h2 := gs_sq (K := K) hp4 hx
  rw [h] at h2
  have hp : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact hp (by linear_combination h2)

theorem gs_map {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : x ^ p = 1) (σ : K →+* K)
    (v : ℕ) (hσ : σ x = x ^ v) (hv : (v : ZMod p) = -1) : σ (gs p hx) = -gs p hx := by
  have hχ : ∀ a : ZMod p, σ (chi p K a) = chi p K a := by
    intro a
    simp only [chi, MulChar.ringHomComp_apply]
    exact map_intCast σ _
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx (-a) := by
    intro a
    calc σ (AddChar.zmodChar p hx a) = (AddChar.zmodChar p hx a) ^ v := by
          rw [AddChar.zmodChar_apply, map_pow, hσ]
          ring
      _ = AddChar.zmodChar p hx (v • a) := by
          exact (AddChar.map_nsmul_eq_pow _ _ _).symm
      _ = AddChar.zmodChar p hx (-a) := by rw [nsmul_eq_mul, hv, neg_one_mul]
  have hc : ∀ a : ZMod p, chi p K a = chi p K (-1) * chi p K (-a) := by
    intro a
    rw [← map_mul, neg_one_mul, neg_neg]
  unfold gs gaussSum
  rw [map_sum]
  simp only [map_mul, hχ, hψ]
  calc ∑ a, chi p K a * AddChar.zmodChar p hx (-a)
        = ∑ a, chi p K (-1) * (chi p K (-a) * AddChar.zmodChar p hx (-a)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hc a, mul_assoc]
    _ = chi p K (-1) * ∑ a, chi p K a * AddChar.zmodChar p hx a := by
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp (Equiv.neg (ZMod p)) (fun a => chi p K a * AddChar.zmodChar p hx a)
    _ = -∑ a, chi p K a * AddChar.zmodChar p hx a := by rw [chi_neg_one (K := K) hp4, neg_one_mul]

end Gauss

section Cyc

abbrev Cyc (m : ℕ) : Type := CyclotomicField m ℚ

instance cycInst (m : ℕ) : IsCyclotomicExtension {m} ℚ (Cyc m) := by
  convert (inferInstance : @IsCyclotomicExtension {m} ℚ (Cyc m) _ _ (CyclotomicField.algebra m ℚ))
  exact Subsingleton.elim _ _

def z (m : ℕ) [NeZero m] : Cyc m := IsCyclotomicExtension.zeta m ℚ (Cyc m)

theorem z_spec (m : ℕ) [NeZero m] : IsPrimitiveRoot (z m) m := by
  exact IsCyclotomicExtension.zeta_spec m ℚ (Cyc m)

theorem pow_mod_of {K : Type*} [Monoid K] {w : K} {N : ℕ} (hw : w ^ N = 1) (a : ℕ) :
    w ^ (a % N) = w ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hw, one_pow, mul_one]

theorem pow_congr_of {K : Type*} [Monoid K] {w : K} {N : ℕ} (hw : w ^ N = 1) {a b : ℕ}
    (h : a % N = b % N) : w ^ a = w ^ b := by
  rw [← pow_mod_of hw a, ← pow_mod_of hw b, h]

theorem splits_of_dvd {L K : Type*} [Field L] [Field K] [Algebra ℚ L] [Algebra ℚ K] (x : L)
    (f : ℚ[X]) (hf : f ≠ 0) (hx : aeval x f = 0) (hs : (f.map (algebraMap ℚ K)).Splits) :
    IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ K)).Splits := by
  have hi : IsIntegral ℚ x := by
    exact IsAlgebraic.isIntegral ⟨f, hf, hx⟩
  refine ⟨hi, ?_⟩
  have hd : (minpoly ℚ x).map (algebraMap ℚ K) ∣ f.map (algebraMap ℚ K) :=
    Polynomial.map_dvd _ (minpoly.dvd ℚ x hx)
  have hf0 : f.map (algebraMap ℚ K) ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective).mpr hf
  exact hs.of_dvd hf0 hd

theorem splits_pow {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} {ξ : K}
    (hξ : IsPrimitiveRoot ξ n) : ((X ^ n - 1 : ℚ[X]).map (algebraMap ℚ K)).Splits := by
  have hm : (X ^ n - 1 : ℚ[X]).map (algebraMap ℚ K) = X ^ n - C 1 := by simp
  rw [hm]
  exact X_pow_sub_one_splits hξ

theorem splits_sq {K : Type*} [Field K] [Algebra ℚ K] (c : ℕ) (g : K) (hg : g ^ 2 = -(c : K)) :
    ((X ^ 2 + C (c : ℚ) : ℚ[X]).map (algebraMap ℚ K)).Splits := by
  have hC : (C g : K[X]) ^ 2 = -(c : K[X]) := by
    rw [← C_pow, hg, C_neg, map_natCast]
  have hm : (X ^ 2 + C (c : ℚ) : ℚ[X]).map (algebraMap ℚ K) = (X - C g) * (X - C (-g)) := by
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      map_natCast, C_neg, Polynomial.map_natCast]
    linear_combination hC
  rw [hm]
  exact (Polynomial.Splits.X_sub_C g).mul (Polynomial.Splits.X_sub_C (-g))

theorem prim_pow {N m : ℕ} [NeZero N] (hm : m ∣ N) : IsPrimitiveRoot (z N ^ (N / m)) m := by
  have hN : N ≠ 0 := NeZero.ne N
  exact (z_spec N).pow (Nat.pos_of_ne_zero hN) (Nat.div_mul_cancel hm).symm

theorem sqrt_exists {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {N : ℕ} [NeZero N] (hp : p ∣ N) :
    ∃ g : Cyc N, g ^ 2 = -(p : Cyc N) := by
  exact ⟨_, gs_sq hp4 (prim_pow hp)⟩

theorem top_adjoin (m : ℕ) [NeZero m] : IntermediateField.adjoin ℚ ({z m} : Set (Cyc m)) = ⊤ := by
  exact IntermediateField.adjoin_eq_top_of_algebra ℚ _
   (IsCyclotomicExtension.adjoin_primitive_root_eq_top (z_spec m))

theorem emb (m N : ℕ) [NeZero m] [NeZero N] (hm : m ∣ N) : Nonempty (Cyc m →ₐ[ℚ] Cyc N) := by
  haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one m ℚ (Cyc m)
  exact ⟨Polynomial.IsSplittingField.lift (Cyc m) (X ^ m - 1 : ℚ[X]) (splits_pow (prim_pow hm))⟩

theorem aut (N : ℕ) [NeZero N] (v : ℕ) (hv : v.Coprime N) :
    ∃ σ : Cyc N ≃ₐ[ℚ] Cyc N, ∀ w : Cyc N, w ^ N = 1 → σ w = w ^ v := by
  have hpos : 0 < N := NeZero.pos N
  have hirr : Irreducible (cyclotomic N ℚ) := cyclotomic.irreducible_rat hpos
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime v hv
  refine ⟨(IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u, fun w hw => ?_⟩
  have hu : (IsCyclotomicExtension.autEquivPow (Cyc N) hirr)
      ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u) = u := MulEquiv.apply_symm_apply _ _
  have hz : (IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u (z N) = z N ^ v := by
    have h2 := (z_spec N).autToPow_spec ℚ ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u)
    have h3 : ((z_spec N).autToPow ℚ ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u) :
        ZMod N) = (v : ZMod N) := by
      rw [show (z_spec N).autToPow ℚ ((IsCyclotomicExtension.autEquivPow (Cyc N) hirr).symm u)
         = u from hu]
      simp [u]
    rw [← h2, h3, ZMod.val_natCast]
    exact pow_mod_of (z_spec N).pow_eq_one v
  obtain ⟨i, -, rfl⟩ := (z_spec N).eq_pow_of_pow_eq_one hw
  rw [map_pow, hz, ← pow_mul, ← pow_mul, mul_comm]

theorem fix {m N : ℕ} [NeZero m] (hm : m ∣ N) (ι : Cyc m →ₐ[ℚ] Cyc N) (σ : Cyc N ≃ₐ[ℚ] Cyc N) (v : ℕ)
    (hσ : ∀ w : Cyc N, w ^ N = 1 → σ w = w ^ v) (hv : v % m = 1 % m) (y : Cyc m) :
    σ (ι y) = ι y := by
  have hext : (σ : Cyc N →ₐ[ℚ] Cyc N).comp ι = ι := by
    apply AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top (z_spec m))
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 : (ι (z m)) ^ m = 1 := by rw [← map_pow, (z_spec m).pow_eq_one, map_one]
    have h2 : (ι (z m)) ^ N = 1 := by
      obtain ⟨k, hk⟩ := hm
      calc ι (z m) ^ N = ι (z m) ^ (m * k) := congrArg (fun n => ι (z m) ^ n) hk
        _ = 1 := by rw [pow_mul, h1, one_pow]
    show σ (ι (z m)) = ι (z m)
    rw [hσ _ h2, pow_congr_of h1 hv, pow_one]
  exact AlgHom.congr_fun hext y

end Cyc

section Div

theorem cop_of_mod_one {v n : ℕ} (h : v % n = 1 % n) : v.Coprime n := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_one_right]

theorem eq_zero_of_neg_eq {K : Type*} [Field K] [CharZero K] {g : K} (h : -g = g) : g = 0 := by
  have h2 : (2 : K) * g = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3

theorem dvd_of_sq {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 3) {m : ℕ} [NeZero m] (y : Cyc m)
    (hy : y ^ 2 = -(p : Cyc m)) : p ∣ m := by
  by_contra hpm
  have hp3 : 3 ≤ p := by omega
  haveI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) hp.out.ne_zero⟩
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm).symm
  obtain ⟨v, hv1, hv2⟩ := Nat.chineseRemainder hcop 1 (p - 1)
  have hvm : v.Coprime m := cop_of_mod_one hv1
  have hvp : v.Coprime p := by
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd hp.out).mpr
    intro hdv
    have h0 : v % p = 0 := Nat.mod_eq_zero_of_dvd hdv
    have h1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : v % p = (p - 1) % p := hv2
    rw [h0, h1] at h2
    omega
  have hv' : (v : ZMod p) = -1 := by
    have h1 : (v : ZMod p) = ((p - 1 : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff' v (p - 1) p).mpr hv2
    rw [h1, Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  obtain ⟨σ, hσ⟩ := aut (m * p) v (Nat.Coprime.mul_right hvm hvp)
  obtain ⟨ι⟩ := emb m (m * p) (dvd_mul_right m p)
  have hσy : σ (ι y) = ι y := fix (dvd_mul_right m p) ι σ v hσ hv1 y
  obtain ⟨x, hx⟩ : ∃ x : Cyc (m * p), IsPrimitiveRoot x p := ⟨_, prim_pow (dvd_mul_left p m)⟩
  have hσx : σ x = x ^ v := hσ x (by rw [pow_mul', hx.pow_eq_one, one_pow])
  have hσg : σ (gs p hx.pow_eq_one) = -gs p hx.pow_eq_one :=
    gs_map hp4 hx.pow_eq_one (σ : Cyc (m * p) →+* Cyc (m * p)) v hσx hv'
  have hyN : (ι y) ^ 2 = -(p : Cyc (m * p)) := by rw [← map_pow, hy, map_neg, map_natCast]
  have hg2 : (gs p hx.pow_eq_one) ^ 2 = -(p : Cyc (m * p)) := gs_sq hp4 hx
  have hfac : (ι y - gs p hx.pow_eq_one) * (ι y + gs p hx.pow_eq_one) = 0 := by
    linear_combination hyN - hg2
  apply gs_ne_zero hp4 hx
  apply eq_zero_of_neg_eq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have e1 : ι y = gs p hx.pow_eq_one := sub_eq_zero.mp h1
    rw [e1] at hσy
    rw [← hσg, hσy]
  · have e2 : ι y = -gs p hx.pow_eq_one := eq_neg_of_add_eq_zero_left h1
    rw [e2, map_neg, neg_inj] at hσy
    rw [← hσg, hσy]

private theorem X_sq_add_C_natCast_ne_zero (c : ℕ) : (X ^ 2 + C (c : ℚ) : ℚ[X]) ≠ 0 := by
  exact (Polynomial.monic_X_pow_add_C _ two_ne_zero).ne_zero

theorem layer_emb {n q d : ℕ} [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {L : Type*} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer n q d ζ a b)
    {N : ℕ} [NeZero N] (h2 : 2 ^ n ∣ N) (hq : q ∣ N) (hd : d ∣ N) :
    Nonempty (L →ₐ[ℚ] Cyc N) := by
  obtain ⟨gq, hgq⟩ := sqrt_exists hq4 hq
  obtain ⟨gd, hgd⟩ := sqrt_exists hd4 hd
  have hne : (X ^ (2 ^ n) - 1 : ℚ[X]) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (pow_pos two_pos n) (1 : ℚ)
  have hfacts : ∀ x ∈ ({ζ, a, b} : Set L),
      IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ (Cyc N))).Splits := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact splits_of_dvd _ (X ^ (2 ^ n) - 1) hne (by simp [h.1.pow_eq_one])
        (splits_pow (prim_pow h2))
    · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero q) (by simp [h.2.1]) (splits_sq q gq hgq)
    · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero d) (by simp [h.2.2.1]) (splits_sq d gd hgd)
  exact IntermediateField.nonempty_algHom_of_adjoin_splits hfacts h.2.2.2

theorem emb_zero {q d : ℕ} [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (0 + 2) q d ζ a b)
    {N : ℕ} [NeZero N] (hq : q ∣ N) (hd : d ∣ N) :
    Nonempty (hostE ζ a b →ₐ[ℚ] Cyc N) := by
  have hζ : IsPrimitiveRoot ζ (2 ^ (0 + 2)) := h.1
  have hz2 : ζ ^ 2 = -1 := by
    have h4 : (ζ ^ 2) ^ 2 = 1 := by
      calc (ζ ^ 2) ^ 2 = ζ ^ (2 ^ (0 + 2)) := by ring
        _ = 1 := hζ.pow_eq_one
    have hne : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have h5 : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd (sub_eq_zero.mp h6) hne
    · linear_combination h6
  have hc : ζ + ζ⁻¹ = 0 := by
    have hinv : ζ⁻¹ = -ζ := inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← sq, hz2, neg_neg])
    rw [hinv]
    ring
  have hE : hostE ζ a b = IntermediateField.adjoin ℚ (({a, b} : Set L) ∪ {ζ + ζ⁻¹}) := by
    unfold hostE E0 F1
    rw [IntermediateField.adjoin_union]
  rw [hE]
  obtain ⟨gq, hgq⟩ := sqrt_exists hq4 hq
  obtain ⟨gd, hgd⟩ := sqrt_exists hd4 hd
  apply IntermediateField.nonempty_algHom_adjoin_of_splits
  intro s hs
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl) | rfl
  · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero q) (by simp [h.2.1]) (splits_sq q gq hgq)
  · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero d) (by simp [h.2.2.1]) (splits_sq d gd hgd)
  · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero 0) (by simp [hc]) (splits_sq 0 0 (by simp))

end Div

section Two

private theorem sq_add_inv_sq_eq_add_inv_sq_sub_two {F : Type*} [Field F] {y : F} (hy : y ≠ 0) :
    y ^ 2 + (y ^ 2)⁻¹ = (y + y⁻¹) ^ 2 - 2 := by
  field_simp
  ring

private theorem pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ {F : Type*} [Field F] {x : F} {n : ℕ}
    (hx : IsPrimitiveRoot x (2 ^ (n + 1))) : x ^ 2 ^ n = -1 := by
  have h4 : (x ^ 2 ^ n) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ]
    exact hx.pow_eq_one
  have hne : x ^ 2 ^ n ≠ 1 :=
    hx.pow_ne_one_of_pos_of_lt (by positivity) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h5 : (x ^ 2 ^ n - 1) * (x ^ 2 ^ n + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd (sub_eq_zero.mp h6) hne
  · linear_combination h6

private theorem pow_two_pow_add_inv_eq_zero_of_isPrimitiveRoot {F : Type*} [Field F] {x : F} {n : ℕ}
    (hx : IsPrimitiveRoot x (2 ^ (n + 2))) : x ^ 2 ^ n + (x ^ 2 ^ n)⁻¹ = 0 := by
  have hy2 : (x ^ 2 ^ n) ^ 2 = -1 := by
    rw [← pow_mul, ← pow_succ]
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ (show IsPrimitiveRoot x (2 ^ (n + 1 + 1)) from hx)
  have hinv : (x ^ 2 ^ n)⁻¹ = -x ^ 2 ^ n :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← sq, hy2, neg_neg])
  rw [hinv]
  ring

theorem two_dvd {e q d : ℕ} (hH : HostHyp q d) (he : e ≠ 0) {L : Type} [Field L]
    [NumberField L] {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) {m : ℕ} [NeZero m]
    (φ : hostE ζ a b →ₐ[ℚ] Cyc m) : 2 ^ (e + 2) ∣ m := by
  by_contra hndvd
  have hζ0 : ζ ≠ 0 := h.1.ne_zero (by positivity)
  obtain ⟨j, m', hm'o, hmj⟩ : ∃ j m', Odd m' ∧ m = 2 ^ j * m' := by
    exact Nat.exists_eq_two_pow_mul_odd (NeZero.ne m)
  have hje : j ≤ e + 1 := by
    by_contra hj
    apply hndvd
    rw [hmj]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (e + 1) * m' := ⟨_, rfl⟩
  have hmM : m ∣ M := by
    rw [hmj, hM]
    exact mul_dvd_mul_right (pow_dvd_pow 2 hje) m'
  have hm'0 : m' ≠ 0 := hm'o.pos.ne'
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero (by positivity) hm'0
  haveI : NeZero M := ⟨hM0⟩
  haveI : NeZero (2 * M) := ⟨mul_ne_zero two_ne_zero hM0⟩
  have hMe : M = 2 * (2 ^ e * m') := by rw [hM]; ring
  have hv2 : (1 + M) % 2 = 1 % 2 := by rw [hMe]; omega
  have hcop : Nat.Coprime (1 + M) (2 * M) :=
    Nat.Coprime.mul_right (cop_of_mod_one hv2) (cop_of_mod_one (Nat.add_mod_right 1 M))
  obtain ⟨σ, hσ⟩ := aut (2 * M) (1 + M) hcop
  obtain ⟨ι⟩ := emb M (2 * M) (dvd_mul_left M 2)
  obtain ⟨ι'⟩ := emb m M hmM
  obtain ⟨ψ, hψ⟩ : ∃ ψ : hostE ζ a b →ₐ[ℚ] Cyc (2 * M), ∀ x, σ (ψ x) = ψ x :=
    ⟨ι.comp (ι'.comp φ), fun x => fix (dvd_mul_left M 2) ι σ (1 + M) hσ (Nat.add_mod_right 1 M) _⟩
  have h2N : 2 ^ (e + 2) ∣ 2 * M := ⟨m', by rw [hM]; ring⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Cyc (2 * M), IsPrimitiveRoot ω (2 ^ (e + 2)) := ⟨_, prim_pow h2N⟩
  have hω0 : ω ≠ 0 := hω.ne_zero (by positivity)
  have hωN : ω ^ (2 * M) = 1 := (hω.pow_eq_one_iff_dvd _).mpr h2N
  have hωM : ω ^ M = -1 := by
    calc ω ^ M = ω ^ (2 ^ (e + 1) * m') := congrArg (fun n => ω ^ n) hM
      _ = (ω ^ 2 ^ (e + 1)) ^ m' := pow_mul ω _ _
      _ = -1 := by
        rw [pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ (show IsPrimitiveRoot ω (2 ^ (e + 1 + 1)) from hω), hm'o.neg_one_pow]
  have hσω : σ ω = -ω := by rw [hσ ω hωN, pow_add, pow_one, hωM, mul_neg_one]
  have h2mem : (2 : L) ∈ hostE ζ a b := by
    simpa using IntermediateField.algebraMap_mem (hostE ζ a b) (2 : ℚ)
  have hF1 : F1 ζ ≤ hostE ζ a b := by
    unfold hostE
    exact le_sup_right
  have hcmem : ∀ j : ℕ, ζ ^ 2 ^ j + (ζ ^ 2 ^ j)⁻¹ ∈ hostE ζ a b := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_one]
      apply hF1
      unfold F1
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    | succ j ih =>
      rw [pow_succ, pow_mul, sq_add_inv_sq_eq_add_inv_sq_sub_two (pow_ne_zero _ hζ0)]
      exact sub_mem (pow_mem ih 2) h2mem
  obtain ⟨C, hCval⟩ : ∃ C : ℕ → hostE ζ a b, ∀ j, (C j : L) = ζ ^ 2 ^ j + (ζ ^ 2 ^ j)⁻¹ :=
    ⟨fun j => ⟨_, hcmem j⟩, fun j => rfl⟩
  have hrec : ∀ j, ψ (C (j + 1)) = ψ (C j) ^ 2 - 2 := by
    intro j
    have hC : C (j + 1) = C j ^ 2 - 2 := by
      apply Subtype.val_injective
      have e1 : ((C j ^ 2 - 2 : hostE ζ a b) : L) = (C j : L) ^ 2 - 2 := by
        rfl
      rw [e1, hCval, hCval, pow_succ, pow_mul, sq_add_inv_sq_eq_add_inv_sq_sub_two (pow_ne_zero _ hζ0)]
    rw [hC, map_sub, map_pow, map_ofNat]
  have hS : ∀ i, i ≤ e → ∃ t, Odd t ∧
      ψ (C (e - i)) = (ω ^ t) ^ 2 ^ (e - i) + ((ω ^ t) ^ 2 ^ (e - i))⁻¹ := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, odd_one, ?_⟩
      have hCe : C e = 0 := Subtype.val_injective (by
        rw [hCval]
        exact pow_two_pow_add_inv_eq_zero_of_isPrimitiveRoot h.1)
      rw [Nat.sub_zero, hCe, map_zero, pow_one, pow_two_pow_add_inv_eq_zero_of_isPrimitiveRoot hω]
    | succ i ih =>
      intro hi
      obtain ⟨t, ht, hteq⟩ := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j, j = e - (i + 1) := ⟨_, rfl⟩
      have hji : e - i = j + 1 := by omega
      rw [← hj]
      rw [hji] at hteq
      obtain ⟨W, hW⟩ : ∃ W, W = (ω ^ t) ^ 2 ^ j := ⟨_, rfl⟩
      have hW0 : W ≠ 0 := by
        rw [hW]
        exact pow_ne_zero _ (pow_ne_zero _ hω0)
      have h1 : (ω ^ t) ^ 2 ^ (j + 1) = W ^ 2 := by
        rw [hW, ← pow_mul (ω ^ t) (2 ^ j) 2, ← pow_succ]
      rw [h1, hrec j, sq_add_inv_sq_eq_add_inv_sq_sub_two hW0] at hteq
      have hsq : (ψ (C j) - (W + W⁻¹)) * (ψ (C j) + (W + W⁻¹)) = 0 := by
        linear_combination hteq
      rcases mul_eq_zero.mp hsq with h2 | h2
      · refine ⟨t, ht, ?_⟩
        rw [← hW]
        linear_combination h2
      · refine ⟨t + 2 ^ (e + 1 - j), ht.add_even (Nat.even_pow.mpr ⟨even_two, by omega⟩), ?_⟩
        have hneg : (ω ^ (t + 2 ^ (e + 1 - j))) ^ 2 ^ j = -W := by
          rw [pow_add, mul_pow, ← pow_mul ω (2 ^ (e + 1 - j)) (2 ^ j), ← pow_add 2 (e + 1 - j) j,
            Nat.sub_add_cancel (by omega : j ≤ e + 1),
            pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ (show IsPrimitiveRoot ω (2 ^ (e + 1 + 1)) from hω), hW]
          ring
        rw [hneg, inv_neg]
        linear_combination h2
  obtain ⟨t, ht, ht0⟩ := hS e le_rfl
  rw [Nat.sub_self, pow_zero, pow_one] at ht0
  have hfix0 := hψ (C 0)
  rw [ht0, map_add, map_inv₀, map_pow, hσω, ht.neg_pow, inv_neg] at hfix0
  have hz : ψ (C 0) = 0 := by
    rw [ht0]
    apply eq_zero_of_neg_eq
    linear_combination hfix0
  have hC0 : C 0 = 0 := by
    exact RingHom.injective ψ.toRingHom (by simpa using hz)
  have hc0 : ζ + ζ⁻¹ = 0 := by
    have h5 := hCval 0
    rw [hC0, pow_zero, pow_one] at h5
    exact h5.symm
  have h4 : ζ ^ 2 + 1 = 0 := by
    have h6 : ζ ^ 2 + 1 = ζ * (ζ + ζ⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ hζ0]
      ring
    rw [h6, hc0, mul_zero]
  have hζ4 : ζ ^ 4 = 1 := by linear_combination (ζ ^ 2 - 1) * h4
  have h48 : 4 < 2 ^ (e + 2) := by
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact h.1.pow_ne_one_of_pos_of_lt (by norm_num) h48 hζ4

end Two

end Cond

open Cond in

theorem hostConductor : HostConductor := by
  unfold HostConductor
  intro e q d hH L _ _ ζ a b h m hm
  have hq : q.Prime := hH.1
  have hd : d.Prime := hH.2.1
  have hq8 : q % 8 = 3 := hH.2.2.1
  have hd16 : d % 16 = 7 := hH.2.2.2.1
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqd : q ≠ d := by omega
  have hE0 : E0 a b ≤ hostE ζ a b := by
    unfold hostE
    exact le_sup_left
  have haE : a ∈ hostE ζ a b := by
    apply hE0
    unfold E0
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  have hbE : b ∈ hostE ζ a b := by
    apply hE0
    unfold E0
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  have hcop : Nat.Coprime q d := (Nat.coprime_primes hq hd).mpr hqd
  constructor
  · rintro ⟨φ⟩
    have hsq : ∀ (x : hostE ζ a b) (c : ℕ), (x : L) ^ 2 = -(c : L) →
        (φ x) ^ 2 = -(c : CyclotomicField m ℚ) := by
      intro x c hx
      have hx' : x ^ 2 = -(c : hostE ζ a b) := Subtype.ext (by simpa using hx)
      rw [← map_pow, hx', map_neg, map_natCast]
    have hqm : q ∣ m := dvd_of_sq hq4 (φ ⟨a, haE⟩) (hsq ⟨a, haE⟩ q h.2.1)
    have hdm : d ∣ m := dvd_of_sq hd4 (φ ⟨b, hbE⟩) (hsq ⟨b, hbE⟩ d h.2.2.1)
    have hqdm : q * d ∣ m := hcop.mul_dvd_of_dvd_of_dvd hqm hdm
    by_cases he : e = 0
    · rw [if_pos he]
      exact hqdm
    · rw [if_neg he, mul_assoc]
      have h2m : 2 ^ (e + 2) ∣ m := two_dvd hH he h φ
      have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
      have h2d : Nat.Coprime 2 d := (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
      exact (Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h2q h2d)).mul_dvd_of_dvd_of_dvd h2m hqdm
  · intro hdiv
    by_cases he : e = 0
    · subst he
      rw [if_pos rfl] at hdiv
      exact emb_zero hq4 hd4 h (dvd_trans (dvd_mul_right q d) hdiv)
        (dvd_trans (dvd_mul_left d q) hdiv)
    · rw [if_neg he] at hdiv
      obtain ⟨f⟩ := layer_emb hq4 hd4 h
        (dvd_trans (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) hdiv)
        (dvd_trans (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) hdiv)
        (dvd_trans (dvd_mul_left _ _) hdiv)
      exact ⟨f.comp (hostE ζ a b).val⟩

end Formalism.FrobeniusOrbits
