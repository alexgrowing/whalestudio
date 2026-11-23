import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.ValExp

noncomputable def halfPow (t : WithTop ℝ) : NNReal :=
  WithTop.recTopCoe (0 : NNReal) (fun r : ℝ => (2⁻¹ : NNReal) ^ r) t

theorem halfPow_top : halfPow ⊤ = 0 := rfl

theorem halfPow_coe (r : ℝ) : halfPow (r : WithTop ℝ) = (2⁻¹ : NNReal) ^ r := rfl

theorem halfPow_zero : halfPow 0 = 1 := by
  rw [← WithTop.coe_zero, halfPow_coe, NNReal.rpow_zero]

theorem halfPow_one : halfPow 1 = 2⁻¹ := by
  rw [← WithTop.coe_one, halfPow_coe, NNReal.rpow_one]

theorem halfPow_add (a b : WithTop ℝ) : halfPow (a + b) = halfPow a * halfPow b := by
  induction a using WithTop.recTopCoe with
  | top => simp [halfPow_top]
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp [halfPow_top]
    | coe b => rw [← WithTop.coe_add, halfPow_coe, halfPow_coe, halfPow_coe, NNReal.rpow_add (by norm_num)]

theorem halfPow_strictAnti : StrictAnti halfPow := by
  intro a b hab
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab not_top_lt
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => rw [halfPow_top, halfPow_coe]; exact NNReal.rpow_pos (by norm_num)
    | coe b =>
      rw [halfPow_coe, halfPow_coe]
      exact NNReal.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by exact_mod_cast hab)

variable {C : Type} [Field C]

noncomputable def mulVal (V : VF C) : Valuation C NNReal where
  toFun x := halfPow (V.v x)
  map_zero' := by rw [V.v.map_zero, halfPow_top]
  map_one' := by rw [V.v.map_one, halfPow_zero]
  map_mul' x y := by rw [V.v.map_mul, halfPow_add]
  map_add_le_max' x y := by
    refine (halfPow_strictAnti.antitone (V.v.map_add x y)).trans ?_
    rcases le_total (V.v x) (V.v y) with h | h
    · rw [min_eq_left h]; exact le_max_left _ _
    · rw [min_eq_right h]; exact le_max_right _ _

theorem mulVal_apply (V : VF C) (x : C) : mulVal V x = halfPow (V.v x) := rfl

theorem mulVal_l (V : VF C) : mulVal V (V.l : C) = 2⁻¹ := by
  rw [mulVal_apply, V.v_l, halfPow_one]

theorem mulVal_le_one_iff (V : VF C) (x : C) : mulVal V x ≤ 1 ↔ V.Ge 0 x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.le_iff_ge]; rfl

theorem mulVal_lt_one_iff (V : VF C) (x : C) : mulVal V x < 1 ↔ V.MM x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.lt_iff_gt]; rfl

theorem ge_l_pow (V : VF C) (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem ge_of_l_pow_mul (V : VF C) (n : ℕ) {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) ^ n * a)) :
    V.Ge (w - n) a := by
  induction n generalizing w with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    refine (ih h.of_l_mul).mono (le_of_eq ?_)
    push_cast; ring

theorem mem_pow_iff (V : VF C) (n : ℕ) (x : (mulVal V).integer) :
    x ∈ (Ideal.span {((V.l : ℕ) : (mulVal V).integer)} ^ n • ⊤ :
      Submodule (mulVal V).integer (mulVal V).integer) ↔ V.Ge n (x : C) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : V.Ge 0 (y : C) := (mulVal_le_one_iff V _).1 y.2
    simpa using (ge_l_pow V n).mul hy
  · intro h
    have hl : (V.l : C) ^ n ≠ 0 := pow_ne_zero _ VF.l_ne_zero
    have hy : V.Ge 0 (((V.l : C) ^ n)⁻¹ * x) := by
      have := ge_of_l_pow_mul V n (w := n) (a := ((V.l : C) ^ n)⁻¹ * x)
        (by rwa [mul_inv_cancel_left₀ hl])
      simpa using this
    refine ⟨⟨_, (mulVal_le_one_iff V _).2 hy⟩, Subtype.ext ?_⟩
    simp [mul_inv_cancel_left₀ hl]

theorem isAdicComplete (V : VF C)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) :
    IsAdicComplete (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) (mulVal V).integer where
  haus' x hx := by
    by_contra h0
    have h1 : (x : C) ≠ 0 := fun h => h0 (Subtype.ext h)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 h1)
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := (mem_pow_iff V n x).1 (SModEq.zero.1 (hx n))
    rw [VF.Ge, ← ht] at this
    exact hn.not_ge (by exact_mod_cast this)
  prec' f hf := by
    obtain ⟨x, hx⟩ := hc (fun n => (f n : C)) fun n => by
      have := (mem_pow_iff V n _).1 (SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm)
      simpa using this
    have h0 : V.Ge 0 x := by
      have h1 : V.Ge 0 (x - f 0) := by simpa using hx 0
      simpa using h1.add ((mulVal_le_one_iff V _).1 (f 0).2)
    refine ⟨⟨x, (mulVal_le_one_iff V _).2 h0⟩, fun n => SModEq.symm (SModEq.sub_mem.2 ?_)⟩
    rw [mem_pow_iff]
    simpa using hx n

theorem exists_mulVal : ∀ (C : Type) [Field C] (V : VF C) [Fact V.l.Prime], (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∃ vm : Valuation C NNReal, ValuationFitting.ValTie V vm ∧ 0 < (vm (V.l : C) : ℝ) ∧ (vm (V.l : C) : ℝ) < 1 ∧ (∀ x : C, vm x ≤ 1 ↔ V.Ge 0 x) ∧ (∀ x : C, vm x < 1 ↔ V.MM x) ∧ IsAdicComplete (Ideal.span {((V.l : ℕ) : vm.integer)}) vm.integer ∧ Nonempty (Algebra ℤ_[V.l] vm.integer) := by
  intro C _ V _ hc
  haveI := isAdicComplete V hc
  refine ⟨mulVal V, fun x hx => ?_, ?_, ?_, mulVal_le_one_iff V, mulVal_lt_one_iff V, this, ?_⟩
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 hx)
    refine ⟨t, ht.symm, ?_⟩
    rw [mulVal_l, mulVal_apply, ← ht, halfPow_coe, NNReal.coe_rpow]
  · rw [mulVal_l]; norm_num
  · rw [mulVal_l]; norm_num
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete
      (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) V.l (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩

end GlobalTheory.ValExp
