import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE

open GlobalTheory.LGrp Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def upLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → Fin n → ℤ) :
    AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j)}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j h => by simp [hX.1 i j h, hY.1 i j h], fun i j h =>
    Valuation.map_add_le _ (hX.2 i j h) (hY.2 i j h)⟩
  neg_mem' := fun {X} hX => ⟨fun i j h => by simp [hX.1 i j h], fun i j h => by simpa using hX.2 i j h⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_upLat {c : Fin n → Fin n → ℤ}
    {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.upLat L c ↔
      (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j) :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in

theorem _root_.GlobalTheory.BorelUMod.mul_mem_upLat {a b c : Fin n → Fin n → ℤ}
    (h : ∀ i j k, i < j → j < k → c i k ≤ a i j + b j k)
    {X Y : Matrix (Fin n) (Fin n) L} (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L a)
    (hY : Y ∈ _root_.GlobalTheory.BorelUMod.upLat L b) : X * Y ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  obtain ⟨hX0, hXv⟩ := hX
  obtain ⟨hY0, hYv⟩ := hY
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · rw [hX0 i k hki, zero_mul]
    · rw [hY0 k j (hji.trans hik.le), mul_zero]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · simp [hX0 i k hki]
    rcases le_or_gt j k with hjk | hkj
    · simp [hY0 k j hjk]
    rw [Valuation.map_mul]
    calc Valued.v (X i k) * Valued.v (Y k j)
        ≤ WithZero.exp (-a i k) * WithZero.exp (-b k j) := mul_le_mul' (hXv i k hik) (hYv k j hkj)
      _ = WithZero.exp (-a i k + -b k j) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-c i j) := WithZero.exp_le_exp.2 (by linarith [h i k j hik hkj])

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.upLat_mono {c C : Fin n → Fin n → ℤ}
    (h : ∀ i j, i < j → c i j ≤ C i j) :
    _root_.GlobalTheory.BorelUMod.upLat L C ≤ _root_.GlobalTheory.BorelUMod.upLat L c :=
  fun _ hX => ⟨hX.1, fun i j hij =>
    (hX.2 i j hij).trans (WithZero.exp_le_exp.2 (neg_le_neg (h i j hij)))⟩

def adjJ (σ : L →+* L) (X : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := fun i j => σ (X j.rev i.rev)

def skewJ (σ : L →+* L) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | adjJ σ X = -X}
  zero_mem' := by ext i j; simp [adjJ]
  add_mem' := fun {X Y} hX hY => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    have h2 := congrFun (congrFun hY i) j
    simp only [adjJ, Matrix.neg_apply] at h1 h2
    simp [adjJ, h1, h2, add_comm]
  neg_mem' := fun {X} hX => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    simp only [adjJ, Matrix.neg_apply] at h1
    simp [adjJ, h1]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.mem_skewJ {σ : L →+* L} {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.skewJ σ n ↔ _root_.GlobalTheory.BorelUMod.adjJ σ X = -X :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mul (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X * Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ Y * _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp only [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.mul_apply, map_sum, map_mul]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_add (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X + Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X + _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_sub (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X - Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X - _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_smul (σ : L →+* L) (a : L) (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (a • X) = σ a • _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_one (σ : L →+* L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [_root_.GlobalTheory.BorelUMod.adjJ]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.one_apply, h, h']

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_adjJ {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x)
    (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (_root_.GlobalTheory.BorelUMod.adjJ σ X) = X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ, hσ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem _root_.GlobalTheory.BorelUMod.mem_GU_iff_adjJ (σ : L →+* L) (g : GL (Fin n) L) :
    g ∈ _root_.Formalism.UG.GU σ n ↔ (g⁻¹).val = _root_.GlobalTheory.BorelUMod.adjJ σ g.val := by
  rw [_root_.GlobalTheory.LGrp.mem_GU_iff]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mem_upLat {σ : L →+* L}
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ}
    (hc : ∀ i j, c j.rev i.rev = c i j) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) :
    _root_.GlobalTheory.BorelUMod.adjJ σ X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · simp [_root_.GlobalTheory.BorelUMod.adjJ, hX.1 j.rev i.rev (Fin.rev_le_rev.2 hji)]
  · simp only [_root_.GlobalTheory.BorelUMod.adjJ]
    rw [hσ, ← hc i j]
    exact hX.2 j.rev i.rev (Fin.rev_lt_rev.2 hij)

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.smul_mem_upLat {c : Fin n → Fin n → ℤ} {a : L}
    (ha : Valued.v a ≤ 1) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) : a • X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => by simp [hX.1 i j hji], fun i j hij => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
  calc Valued.v a * Valued.v (X i j) ≤ 1 * WithZero.exp (-c i j) := mul_le_mul' ha (hX.2 i j hij)
    _ = WithZero.exp (-c i j) := one_mul _

def IsWeight (c : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, c j.rev i.rev = c i j) ∧ ∀ i j k, i < j → j < k → c i k ≤ c i j + c j k

def IsIdealWeight (c C : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, i < j → c i j ≤ C i j) ∧ (∀ i j k, i < j → j < k → C i k ≤ c i j + C j k) ∧
    ∀ i j k, i < j → j < k → C i k ≤ C i j + c j k

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.isWeight_zero :
    _root_.GlobalTheory.BorelUMod.IsWeight (fun _ _ : Fin n => (0 : ℤ)) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => by simp⟩

def unipLat {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ} (hc : IsWeight c) :
    Subgroup (borelU σ n).U where
  carrier := {u | (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ upLat L c}
  one_mem' := by
    show ((1 : Matrix (Fin n) (Fin n) L)) - 1 ∈ upLat L c
    simp
  mul_mem' := fun {u w} hu hw => by
    show u.1.1.val * w.1.1.val - 1 ∈ upLat L c
    have : u.1.1.val * w.1.1.val - 1 = (u.1.1.val - 1) * (w.1.1.val - 1) + (u.1.1.val - 1) + (w.1.1.val - 1) := by
      noncomm_ring
    rw [this]
    exact add_mem (add_mem (mul_mem_upLat hc.2 hu hw) hu) hw
  inv_mem' := fun {u} hu => by
    show (u.1.1⁻¹).val - 1 ∈ upLat L c
    rw [(mem_GU_iff_adjJ σ _).1 u.1.2, ← adjJ_one σ, ← adjJ_sub]
    exact adjJ_mem_upLat hσ hc.1 hu

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_unipLat {σ : L →+* L}
    {hσ : ∀ x, Valued.v (σ x) = Valued.v x} {c : Fin n → Fin n → ℤ}
    {hc : _root_.GlobalTheory.BorelUMod.IsWeight c} {u : (_root_.GlobalTheory.LGrp.borelU σ n).U} :
    u ∈ _root_.GlobalTheory.BorelUMod.unipLat hσ hc ↔
      (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ _root_.GlobalTheory.BorelUMod.upLat L c :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in

theorem _root_.GlobalTheory.BorelUMod.exists_trace_one {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : _root_.Formalism.UG.IsUnramInv ϖ σ q) :
    (∃ θ : L, Valued.v θ ≤ 1 ∧ θ + σ θ = 1) ∧ ∃ d : L, Valued.v d = 1 ∧ σ d = -d := by
  obtain ⟨hinv, -, -, -, ⟨x, hx, hxu⟩, -⟩ := h
  have hx1 : Valued.v x ≤ 1 := hx
  refine ⟨?_, σ x - x, hxu, by rw [map_sub, hinv]; ring⟩
  have h2le : Valued.v (2 : L) ≤ 1 := by
    have h11 : Valued.v ((1 : L) + 1) ≤ 1 :=
      Valuation.map_add_le _ (le_of_eq (Valuation.map_one _)) (le_of_eq (Valuation.map_one _))
    rwa [one_add_one_eq_two] at h11
  rcases h2le.lt_or_eq with h2 | h2
  · have hlt : Valued.v (2 * x) < Valued.v (σ x - x) := by
      rw [hxu, Valuation.map_mul]
      calc Valued.v (2 : L) * Valued.v x ≤ Valued.v (2 : L) * 1 := mul_le_mul' le_rfl hx1
        _ = Valued.v (2 : L) := mul_one _
        _ < 1 := h2
    have ht : Valued.v (x + σ x) = 1 := by
      have e : x + σ x = (σ x - x) + 2 * x := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ hlt, hxu]
    have ht0 : x + σ x ≠ 0 := by
      intro e
      rw [e, Valuation.map_zero] at ht
      exact zero_ne_one ht
    refine ⟨x / (x + σ x), ?_, ?_⟩
    · rw [map_div₀, ht, div_one]
      exact hx1
    · rw [map_div₀, map_add, hinv, add_comm (σ x) x, ← add_div, div_self ht0]
  · refine ⟨1 / 2, ?_, ?_⟩
    · rw [map_div₀, Valuation.map_one, h2, div_one]
    · rw [map_div₀, map_one, map_ofNat]
      have h20 : (2 : L) ≠ 0 := by
        intro e
        rw [e, Valuation.map_zero] at h2
        exact zero_ne_one h2
      rw [← add_div, one_add_one_eq_two, div_self h20]

end GlobalTheory.BorelUMod
