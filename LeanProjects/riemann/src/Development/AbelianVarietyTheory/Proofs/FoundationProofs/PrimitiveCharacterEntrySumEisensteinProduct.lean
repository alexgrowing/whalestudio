import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DropConst

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem isUnit_iff_not_dvd_val (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (c : ZMod (p ^ m)) :
    IsUnit c ↔ ¬ p ∣ c.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem isUnit_natCast_of_not_dvd (p m N : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) : IsUnit (N : ZMod (p ^ m)) := by
  have hp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m

omit [CharZero K] in

theorem sum_pick (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (x z : ℤ) (F : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, (if z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then F u else 0) =
    if ¬ (p : ℤ) ∣ z ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N] then
      F ((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) else 0 := by
  have hp : p.Prime := Fact.out
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have h1 : (N : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) = 1 := Ring.mul_inverse_cancel _ hU
  have hP : (p : ZMod (p ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hcop : (N : ℤ).natAbs.Coprime ((p ^ m : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m
  have key : ∀ u : ZMod (p ^ m), z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] ↔
      (u = (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N]) := by
    intro u
    rw [Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hcop, and_comm]
    refine and_congr ?_ ?_
    · rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, hP, zero_mul, add_zero]
      constructor
      · intro h; rw [h]; linear_combination (-u) * h1
      · intro h; rw [h]; linear_combination (-(z : ZMod (p ^ m))) * h1
    · rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, add_sub_assoc]
      exact dvd_add_right (dvd_mul_right _ _)
  have hmem : (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∈ primeTo p m ↔ ¬ (p : ℤ) ∣ z := by
    rw [primeTo, mem_filter, ← isUnit_iff_not_dvd_val p m hm, ← dvd_val_iff p m hm, ← isUnit_iff_not_dvd_val p m hm,
      IsUnit.mul_iff]
    simp [hU.ringInverse]
  simp only [key]
  by_cases hx : z ≡ (p : ℤ) ^ m * x [ZMOD N]
  · simp only [hx, and_true, sum_ite_eq', hmem]
  · simp [hx]

theorem row_sum (p m N j : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (ζ : K) (x : ℤ) (s : ZMod (p ^ m) → ℤ)
    (Φ : ZMod (p ^ m) → ZMod (p ^ m) → K) (n : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m),
      Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
    ∑ q ∈ (n : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ (p : ℤ) ^ m * x [ZMOD N] then
      (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
        ∑ a : ZMod (p ^ m), Φ ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) a * ζ ^ (s a * q.2)
      else 0 := by
  have e : ∀ u : ZMod (p ^ m),
      ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
      ∑ q ∈ (n : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then
        (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
          ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2) else 0 := by
    intro u
    simp_rw [coefPos_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    split_ifs
    · exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl fun u _ => e u, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  exact sum_pick p m N hm hpN x q.1 (fun u => (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
    ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2))

theorem col_sum_div (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (n₁ n₂ d d' : ℤ) (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m),
      ψ ((n₁ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) * b -
        a * ((n₂ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
        ζ ^ ((N : ℤ) * b.val * d')) * ζ ^ ((N : ℤ) * a.val * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (N : ZMod (p ^ m))) *
          ψ⁻¹ (d' : ZMod (p ^ m)) else 0 := by
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have hI := hU.ringInverse
  have hval : ∀ z : ℤ, ¬ (p : ℤ) ∣ z →
      ¬ (p : ℤ) ∣ ((((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))).val : ℕ) : ℤ) := by
    intro z hz
    rw [Int.natCast_dvd_natCast, ← isUnit_iff_not_dvd_val p m hm]
    refine IsUnit.mul ?_ hI
    rwa [isUnit_iff_not_dvd_val p m hm, dvd_val_iff p m hm]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  have h := col_sum p m N hm hN ψ hψ ζ hζ 0 0 _ _ d d' (hval n₁ h₁) (hval n₂ h₂)
  simp only [mul_zero, add_zero, zero_mul, zpow_zero, mul_one, hdvd, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] at h
  rw [h, map_mul, ← MulChar.inv_apply]
  refine if_congr (and_congr_left' ?_) rfl rfl
  rw [hdvd, ← hI.mul_left_eq_zero (a := ((n₁ * d + n₂ * d' : ℤ) : ZMod (p ^ m)))]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem entry_sum (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (hm : 1 ≤ m) (hN : 0 < N)
    (hpN : ¬ p ∣ N) (_hk : 3 ≤ k) (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
    if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
      (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  have hx : ∀ c z : ℤ, z ≡ (p : ℤ) ^ m * (c * t) [ZMOD N] ↔ z ≡ c [ZMOD N] := by
    intro c z
    have h : (p : ℤ) ^ m * (c * t) ≡ c [ZMOD N] := by
      have := ht.mul_left c
      rwa [mul_one, mul_left_comm] at this
    exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  have e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
      (∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) *
      coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i := by
    intro u a
    have := row_sum p m N 1 hm hpN ζ (b₀ * t) (fun b => (N : ℤ) * b.val) (fun v b => ψ (u * b - a * v)) j
    simp only [Nat.sub_self, pow_zero, mul_one, hx] at this
    rw [← this]
    simp only [sum_mul]
    exact sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring
  simp only [e1]
  rw [row_sum p m N (k - 1) hm hpN ζ (a₀ * t) (fun a => (N : ℤ) * a.val)
    (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) i]
  have e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K),
      (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) =
      ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0 := by
    intro c _ C A B
    split_ifs
    · rw [sum_mul_sum]; simp only [mul_sum]
    · simp
  rw [ffMu_eq, eeMu_eq, e2]
  refine sum_congr rfl fun q hq => ?_
  simp only [hx]
  by_cases h₁ : (p : ℤ) ∣ q.1
  · simp [h₁]
  by_cases g₁ : q.1 ≡ a₀ [ZMOD N]
  swap
  · simp [g₁]
  rw [if_pos ⟨h₁, g₁⟩]
  simp only [sum_mul (j : ℤ).divisorsAntidiag]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun q' hq' => ?_
  by_cases h₂ : (p : ℤ) ∣ q'.1
  · simp [h₂]
  by_cases g₂ : q'.1 ≡ b₀ [ZMOD N]
  swap
  · simp [g₂]
  simp only [if_pos (And.intro h₂ g₂), mul_assoc (q'.2.sign : K)]
  rw [← mul_sum, col_sum_div p m N hm hN hpN ψ hψ ζ hζ q.1 q'.1 q.2 q'.2 h₁ h₂,
    (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]
  have hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j := by norm_cast
  simp only [hc]
  rw [show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]
  by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>
    simp only [a1, a2, a3, h₁, h₂, g₁, g₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false,
      mul_zero, zero_mul, false_and]
  ring

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
