import Mathlib
import GroundTheory.LocalFields.LocalFourierTrace

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory
open scoped NNReal ENNReal

section DifferentNorm

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem card_quotient_differentIdeal :
    Nat.card (𝒪[L] ⧸ differentIdeal 𝒪[K] 𝒪[L]) = residueCard L ^ differentExponent K L := by
  rw [differentIdeal_eq_maximalIdeal_pow, ← Submodule.cardQuot_apply,
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[L]),
    Submodule.cardQuot_apply]
  rfl

end DifferentNorm

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_integer_iff_norm_le_one (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := _root_.Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

def padicIntRingEquivInteger : ℤ_[p] ≃+* 𝒪[ℚ_[p]] where
  toFun x := ⟨x, (mem_integer_iff_norm_le_one p x).mpr x.2⟩
  invFun y := ⟨y, (mem_integer_iff_norm_le_one p y).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem irreducible_p_integer : Irreducible (p : 𝒪[ℚ_[p]]) := by
  have h := (MulEquiv.irreducible_iff (f := (padicIntRingEquivInteger p).toMulEquiv)
    (x := (p : ℤ_[p]))).2 PadicInt.irreducible_p
  simpa using h

theorem ord_p : ord (p : ℚ_[p]) = 1 := by
  have := ord_uniformizer (irreducible_p_integer p)
  simpa using this

theorem fourierChar_intCast (n : ℤ) : Real.fourierChar (n : ℝ) = 1 := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  exact ⟨n, by ring⟩

theorem exists_int_of_norm_le_one {N : ℤ} {j : ℕ}
    (h : ‖(N : ℚ_[p]) / (p : ℚ_[p]) ^ j‖ ≤ 1) : ∃ n : ℤ, (N : ℚ) / (p : ℚ) ^ j = n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_div, norm_pow, _root_.Padic.norm_p, div_le_one (pow_pos (inv_pos.mpr hp0) j)] at h
  have h' : ‖(N : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨n, hn⟩ := (_root_.Padic.norm_int_le_pow_iff_dvd N j).mp h'
  refine ⟨n, ?_⟩
  have : (p : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [hn, div_eq_iff this]
  push_cast
  ring

theorem exists_norm_sub_le_one (x : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ), ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1 := by
  have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    refine ⟨x.valuation.natAbs, ?_⟩
    rw [norm_mul, norm_pow, _root_.Padic.norm_p, _root_.Padic.norm_eq_zpow_neg_valuation hx,
      inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
    apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le)
    omega
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k ⟨_, hk⟩)
  refine ⟨PadicInt.appr ⟨_, hk⟩ k, k, ?_⟩
  have hz' : (z : ℚ_[p]) * (p : ℚ_[p]) ^ k =
      (p : ℚ_[p]) ^ k * x - (PadicInt.appr ⟨_, hk⟩ k : ℚ_[p]) := by
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] at this
    exact this
  have hpk : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ hpp
  have e : x - (PadicInt.appr ⟨_, hk⟩ k : ℚ_[p]) / (p : ℚ_[p]) ^ k = (z : ℚ_[p]) := by
    have h2 : (x - (PadicInt.appr ⟨_, hk⟩ k : ℚ_[p]) / (p : ℚ_[p]) ^ k) * (p : ℚ_[p]) ^ k =
        (z : ℚ_[p]) * (p : ℚ_[p]) ^ k := by
      rw [sub_mul, div_mul_cancel₀ _ hpk, hz']
      ring
    exact mul_right_cancel₀ hpk h2
  push_cast
  rw [e]
  exact z.2

theorem fourierChar_eq_of_norm_sub_le_one {m m' : ℤ} {k k' : ℕ}
    (h : ‖(m : ℚ_[p]) / (p : ℚ_[p]) ^ k - (m' : ℚ_[p]) / (p : ℚ_[p]) ^ k'‖ ≤ 1) :
    Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) =
      Real.fourierChar (((m' : ℚ) / (p : ℚ) ^ k' : ℚ) : ℝ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e : (m : ℚ_[p]) / (p : ℚ_[p]) ^ k - (m' : ℚ_[p]) / (p : ℚ_[p]) ^ k' =
      ((m * (p : ℤ) ^ k' - m' * (p : ℤ) ^ k : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ (k + k') := by
    push_cast
    field_simp
    ring
  rw [e] at h
  obtain ⟨n, hn⟩ := exists_int_of_norm_le_one p h
  have e' : (m : ℚ) / (p : ℚ) ^ k = (m' : ℚ) / (p : ℚ) ^ k' + n := by
    rw [← hn]
    push_cast
    field_simp
    ring
  rw [e', Rat.cast_add, Rat.cast_intCast, AddChar.map_add_eq_mul, fourierChar_intCast, mul_one]

def fracRep (x : ℚ_[p]) : ℚ :=
  ((Classical.choose (exists_norm_sub_le_one p x) : ℤ) : ℚ) /
    (p : ℚ) ^ Classical.choose (Classical.choose_spec (exists_norm_sub_le_one p x))

theorem fracRep_spec (x : ℚ_[p]) : ∃ (m : ℤ) (k : ℕ), fracRep p x = (m : ℚ) / (p : ℚ) ^ k ∧
    ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1 :=
  ⟨_, _, rfl, Classical.choose_spec (Classical.choose_spec (exists_norm_sub_le_one p x))⟩

def stdCharFun (x : ℚ_[p]) : Circle := Real.fourierChar (fracRep p x : ℝ)

theorem stdCharFun_eq (x : ℚ_[p]) (m : ℤ) (k : ℕ)
    (h : ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1) :
    stdCharFun p x = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) := by
  obtain ⟨m₀, k₀, e₀, h₀⟩ := fracRep_spec p x
  rw [stdCharFun, e₀]
  apply fourierChar_eq_of_norm_sub_le_one
  calc ‖(m₀ : ℚ_[p]) / (p : ℚ_[p]) ^ k₀ - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖
      = ‖(x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k) + -(x - (m₀ : ℚ_[p]) / (p : ℚ_[p]) ^ k₀)‖ := by
        congr 1
        ring
    _ ≤ max ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ‖-(x - (m₀ : ℚ_[p]) / (p : ℚ_[p]) ^ k₀)‖ :=
        _root_.Padic.nonarchimedean _ _
    _ ≤ 1 := max_le h (by rwa [norm_neg])

def stdChar : AddChar ℚ_[p] Circle where
  toFun := stdCharFun p
  map_zero_eq_one' := by
    rw [stdCharFun_eq p 0 0 0 (by simp)]
    simp
  map_add_eq_mul' x y := by
    obtain ⟨mx, kx, ex, hx⟩ := fracRep_spec p x
    obtain ⟨my, ky, ey, hy⟩ := fracRep_spec p y
    have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hxy : ‖(x + y) - ((mx * (p : ℤ) ^ ky + my * (p : ℤ) ^ kx : ℤ) : ℚ_[p]) /
        (p : ℚ_[p]) ^ (kx + ky)‖ ≤ 1 := by
      have e : (x + y) - ((mx * (p : ℤ) ^ ky + my * (p : ℤ) ^ kx : ℤ) : ℚ_[p]) /
          (p : ℚ_[p]) ^ (kx + ky) = (x - (mx : ℚ_[p]) / (p : ℚ_[p]) ^ kx) +
            (y - (my : ℚ_[p]) / (p : ℚ_[p]) ^ ky) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact (_root_.Padic.nonarchimedean _ _).trans (max_le hx hy)
    rw [stdCharFun_eq p _ _ _ hxy, stdCharFun_eq p _ _ _ hx, stdCharFun_eq p _ _ _ hy,
      ← AddChar.map_add_eq_mul, ← Rat.cast_add]
    congr 2
    push_cast
    field_simp
    ring

theorem stdChar_apply (x : ℚ_[p]) (m : ℤ) (k : ℕ) (h : ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1) :
    stdChar p x = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) :=
  stdCharFun_eq p x m k h

theorem stdChar_intCast_div_pow (m : ℤ) (k : ℕ) :
    stdChar p ((m : ℚ_[p]) / (p : ℚ_[p]) ^ k) = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) :=
  stdChar_apply p _ m k (by simp)

theorem stdChar_eq_one_of_norm_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : stdChar p x = 1 := by
  rw [stdChar_apply p x 0 0 (by simpa using hx)]
  simp

theorem stdChar_inv_p_ne_one : stdChar p (p : ℚ_[p])⁻¹ ≠ 1 := by
  have h := stdChar_intCast_div_pow p 1 1
  rw [Int.cast_one, pow_one, one_div] at h
  rw [h, Real.fourierChar_apply', Ne, Circle.exp_eq_one]
  rintro ⟨n, hn⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h1 : (1 : ℝ) = n * p := by
    push_cast at hn
    field_simp at hn
    nlinarith [Real.pi_pos]
  have h2 : (n : ℤ) * p = 1 := by exact_mod_cast h1.symm
  have h3 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) ⟨n, by rw [← h2]; ring⟩
  have : p = 1 := by exact_mod_cast h3
  exact hp.out.one_lt.ne' this

theorem isTrivialOn_stdChar_zero : IsTrivialOn (stdChar p) 0 := fun x hx =>
  stdChar_eq_one_of_norm_le_one p ((mem_integer_iff_norm_le_one p x).mp (mem_valBall_zero_iff.mp hx))

theorem not_isTrivialOn_stdChar_neg_one : ¬ IsTrivialOn (stdChar p) (-1) := by
  intro h
  have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply stdChar_inv_p_ne_one p
  apply h
  rw [mem_valBall_iff_le_ord (inv_ne_zero hpp), ord_inv hpp, ord_p]

theorem continuous_stdChar : Continuous (stdChar p) :=
  continuous_of_isTrivialOn (isTrivialOn_stdChar_zero p)

theorem stdChar_ne_one : stdChar p ≠ 1 := by
  intro h
  apply not_isTrivialOn_stdChar_neg_one p
  rw [h]
  intro x _
  exact AddChar.one_apply x

theorem addCharConductor_stdChar : addCharConductor (stdChar p) = 0 := by
  have hc := continuous_stdChar p
  have hne := stdChar_ne_one p
  refine le_antisymm ((isTrivialOn_iff hc hne 0).mp (isTrivialOn_stdChar_zero p)) ?_
  by_contra hlt
  exact not_isTrivialOn_stdChar_neg_one p ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

def stdCharOf : AddChar K Circle := traceChar K (stdChar p)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
theorem stdCharOf_apply (x : K) : stdCharOf p K x = stdChar p (Algebra.trace ℚ_[p] K x) := rfl

theorem continuous_stdCharOf : Continuous (stdCharOf p K) :=
  continuous_traceChar (continuous_stdChar p) (stdChar_ne_one p)

theorem stdCharOf_ne_one : stdCharOf p K ≠ 1 :=
  traceChar_ne_one (continuous_stdChar p) (stdChar_ne_one p)

theorem addCharConductor_stdCharOf :
    addCharConductor (stdCharOf p K) = -(differentExponent ℚ_[p] K : ℤ) :=
  addCharConductor_traceChar_of_eq_zero (continuous_stdChar p) (stdChar_ne_one p)
    (addCharConductor_stdChar p)

variable [MeasurableSpace K] [BorelSpace K]

theorem selfDualMeasure_stdCharOf_integers_eq_rpow :
    selfDualMeasure (stdCharOf p K) (𝒪[K] : Set K) =
      ((residueCard K : ℝ≥0) ^ (-(differentExponent ℚ_[p] K : ℝ) / 2) : ℝ≥0) := by
  rw [selfDualMeasure_integers, addCharConductor_stdCharOf]
  push_cast
  rfl

theorem selfDualMeasure_stdCharOf_integers :
    selfDualMeasure (stdCharOf p K) (𝒪[K] : Set K) =
      ((Nat.card (𝒪[K] ⧸ differentIdeal 𝒪[ℚ_[p]] 𝒪[K]) : ℝ≥0) ^ (-(1 / 2 : ℝ)) : ℝ≥0) := by
  rw [selfDualMeasure_stdCharOf_integers_eq_rpow, card_quotient_differentIdeal, Nat.cast_pow,
    ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  congr 2
  ring

end Extension

end Padic

end GroundTheory.LocalField
