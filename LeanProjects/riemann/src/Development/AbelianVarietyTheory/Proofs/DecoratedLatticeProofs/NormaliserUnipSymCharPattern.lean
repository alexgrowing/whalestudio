import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle

noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.SymNorm

variable {k : Type} [Field k] {n : ℕ}

def Prec (ρ κ i j : ℕ) : Prop := i < j ∧ ¬(ρ ≤ i ∧ i < ρ + κ ∧ j = ρ + κ)

def ht (ρ κ i : ℕ) : ℕ := if i < ρ + κ then i else if i = ρ + κ then ρ else i - 1

def dp (n ρ κ i : ℕ) : ℕ := if i < ρ + κ then n - 2 - i else if i = ρ + κ then ρ else n - 1 - i

theorem ht_lt {ρ κ i j : ℕ} (hκ : 1 ≤ κ) (h : Prec ρ κ i j) : ht ρ κ i + 1 ≤ ht ρ κ j := by
  unfold Prec at h; unfold ht; split_ifs <;> omega

theorem dp_lt {n ρ κ i j : ℕ} (hn : n = 2 * ρ + κ + 1) (hκ : 1 ≤ κ) (hj : j < n) (h : Prec ρ κ i j) : dp n ρ κ j + 1 ≤ dp n ρ κ i := by
  unfold Prec at h; unfold dp; split_ifs <;> (try rw [Nat.sub_sub, Nat.sub_sub]) <;> omega

theorem exists_succ {ρ κ : ℕ} (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (a : Fin n) (ha : 1 ≤ dp n ρ κ a.val) :
    ∃ q : Fin n, Prec ρ κ a.val q.val ∧ dp n ρ κ a.val ≤ dp n ρ κ q.val + 1 := by
  by_cases h : a.val + 1 = ρ + κ
  · refine ⟨⟨ρ + κ + 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, dp, Fin.val_mk] at *; split_ifs at * <;> omega)
  · have : a.val + 1 < n := by unfold dp at ha; split_ifs at ha <;> omega
    refine ⟨⟨a.val + 1, this⟩, ?_, ?_⟩
    all_goals (simp only [Prec, dp, Fin.val_mk] at *; split_ifs at * <;> omega)

theorem exists_pred {ρ κ : ℕ} (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (a : Fin n) (ha : 1 ≤ ht ρ κ a.val) :
    ∃ c : Fin n, Prec ρ κ c.val a.val ∧ ht ρ κ a.val ≤ ht ρ κ c.val + 1 := by
  have := a.2
  by_cases h : a.val = ρ + κ
  · refine ⟨⟨ρ - 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, ht, Fin.val_mk] at *; split_ifs at * <;> omega)
  by_cases h' : a.val = ρ + κ + 1
  · refine ⟨⟨ρ + κ - 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, ht, Fin.val_mk] at *; split_ifs at * <;> omega)
  · have : 1 ≤ a.val := by unfold ht at ha; split_ifs at ha <;> omega
    refine ⟨⟨a.val - 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, ht, Fin.val_mk] at *; split_ifs at * <;> omega)

theorem allowed_of {ρ κ i a : ℕ} (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hi : i < n) (ha : a < n)
    (h1 : dp n ρ κ a ≤ dp n ρ κ i) (h2 : ht ρ κ i ≤ ht ρ κ a) :
    i = a ∨ Prec ρ κ i a ∨ (i = ρ ∧ a = ρ + κ) ∨ (i = ρ + κ ∧ a + 1 = ρ + κ) := by
  unfold Prec; unfold dp at h1; unfold ht at h2; split_ifs at h1 h2 <;> omega

section Pattern

variable {ρ κ : ℕ} {X Y : Matrix (Fin n) (Fin n) k}

theorem step_up (hYX : Y * X = 1)
    (hP : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → X i p * Y q j = 0)
    {i p q : Fin n} (hip : X i p ≠ 0) (hpq : Prec ρ κ p q) : ∃ j : Fin n, Prec ρ κ i j ∧ X j q ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 : (Y * X) q q = 0 := by
    rw [mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : Prec ρ κ i j
    · rw [hc j hj, mul_zero]
    · rw [(mul_eq_zero.1 (hP p q hpq i j hj)).resolve_left hip, zero_mul]
  rw [hYX, one_apply_eq] at h0
  exact one_ne_zero h0

theorem step_down (hXY : X * Y = 1)
    (hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → Y i p * X q j = 0)
    {i a c : Fin n} (hia : X i a ≠ 0) (hci : Prec ρ κ c i) : ∃ j : Fin n, Prec ρ κ j a ∧ X c j ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 : (X * Y) c c = 0 := by
    rw [mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : Prec ρ κ j a
    · rw [hc j hj, zero_mul]
    · rw [(mul_eq_zero.1 (hP' c i hci j a hj)).resolve_right hia, mul_zero]
  rw [hXY, one_apply_eq] at h0
  exact one_ne_zero h0

theorem dp_le (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hYX : Y * X = 1)
    (hP : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → X i p * Y q j = 0) :
    ∀ d : ℕ, ∀ i a : Fin n, X i a ≠ 0 → d ≤ dp n ρ κ a → d ≤ dp n ρ κ i := by
  intro d
  induction d with
  | zero => intros; exact Nat.zero_le _
  | succ d ih =>
    intro i a hia hd
    obtain ⟨q, haq, hq⟩ := exists_succ hn hρ a (by omega)
    obtain ⟨j, hij, hjq⟩ := step_up hYX hP hia haq
    have h1 := ih j q hjq (by omega)
    have h2 := dp_lt hn (by omega) j.2 hij
    omega

theorem ht_le (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hXY : X * Y = 1)
    (hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → Y i p * X q j = 0) :
    ∀ d : ℕ, ∀ i a : Fin n, X i a ≠ 0 → d ≤ ht ρ κ i → d ≤ ht ρ κ a := by
  intro d
  induction d with
  | zero => intros; exact Nat.zero_le _
  | succ d ih =>
    intro i a hia hd
    obtain ⟨c, hci, hc⟩ := exists_pred hn hρ hκ i (by omega)
    obtain ⟨j, hja, hcj⟩ := step_down hXY hP' hia hci
    have h1 := ih c j hcj (by omega)
    have h2 := ht_lt (by omega) hja
    omega

theorem pattern (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hP : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → X i p * Y q j = 0)
    (hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → Y i p * X q j = 0)
    (i a : Fin n) (h : X i a ≠ 0) :
    i.val = a.val ∨ Prec ρ κ i a ∨ (i.val = ρ ∧ a.val = ρ + κ) ∨ (i.val = ρ + κ ∧ a.val + 1 = ρ + κ) :=
  allowed_of hn hρ hκ i.2 a.2 (dp_le hn hρ hκ hYX hP _ i a h le_rfl) (ht_le hn hρ hκ hXY hP' _ i a h le_rfl)

end Pattern

section Conj

theorem mul_single_mul' (X Y : Matrix (Fin n) (Fin n) k) (p q i j : Fin n) (s : k) :
    (X * single p q s * Y) i j = X i p * s * Y q j := by
  have h1 : X * single p q s = Matrix.of fun i x => if x = q then X i p * s else 0 := by
    ext i x
    rw [Matrix.mul_apply, Matrix.of_apply]
    by_cases hx : x = q
    · subst hx
      rw [if_pos rfl, Finset.sum_eq_single p]
      · simp [Matrix.single_apply]
      · intro y _ hy; simp [Matrix.single_apply, Ne.symm hy]
      · simp
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun y _ => by simp [Matrix.single_apply, Ne.symm hx]
  rw [h1, Matrix.mul_apply, Finset.sum_eq_single q]
  · simp [mul_assoc]
  · intro y _ hy; simp [hy]
  · simp

def elemU (p q : Fin n) (hpq : p ≠ q) (s : k) : GL (Fin n) k :=
  have hEE : single p q s * single p q s = 0 := by simp [hpq.symm]
  ⟨1 + single p q s, 1 - single p q s,
    by rw [add_mul, one_mul, mul_sub, hEE, sub_zero, mul_one, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, hEE, add_zero, mul_one, add_sub_cancel_right]⟩

theorem elemU_apply (p q : Fin n) (hpq : p ≠ q) (s : k) (i j : Fin n) :
    ((elemU p q hpq s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (1 : Matrix (Fin n) (Fin n) k) i j + single p q s i j := rfl

theorem elemU_mem {ρ κ : ℕ} {p q : Fin n} (h : Prec ρ κ p q) (hpq : p ≠ q) (s : k) :
    elemU p q hpq s ∈ unipSym k n ρ κ := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.val < i.val := hij
    rw [elemU_apply, one_apply_ne (fun e => by rw [e] at hij'; omega), single_apply, if_neg, zero_add]
    rintro ⟨rfl, rfl⟩; unfold Prec at h; omega
  · rw [elemU_apply, one_apply_eq, single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩; exact hpq rfl
  · rw [elemU_apply, one_apply_ne (fun e => by rw [e] at h1; omega), single_apply, if_neg, zero_add]
    rintro ⟨rfl, rfl⟩; unfold Prec at h; omega

theorem conj_elemU_apply (M : GL (Fin n) k) (p q : Fin n) (hpq : p ≠ q) (s : k) (i j : Fin n) :
    ((M * elemU p q hpq s * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (1 : Matrix (Fin n) (Fin n) k) i j +
        (M : Matrix (Fin n) (Fin n) k) i p * s * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) q j := by
  have : ((M * elemU p q hpq s * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + (M : Matrix (Fin n) (Fin n) k) * single p q s * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [Units.val_mul, Units.val_mul]
    show (M : Matrix (Fin n) (Fin n) k) * (1 + single p q s) * _ = _
    rw [mul_add, mul_one, add_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [this, Matrix.add_apply, mul_single_mul']

theorem unipSym_entry {ρ κ : ℕ} {g : GL (Fin n) k} (hg : g ∈ unipSym k n ρ κ) {i j : Fin n} (h : ¬ Prec ρ κ i j) :
    (g : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  rcases lt_trichotomy i.val j.val with h1 | h1 | h1
  · have h3 : ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ := by
      by_contra hc; exact h ⟨h1, hc⟩
    rw [hg.2 i j h3.1 h3.2.1 h3.2.2, one_apply_ne (fun e => by rw [e] at h1; omega)]
  · have := Fin.ext h1; subst this; rw [hg.1.2 i, one_apply_eq]
  · rw [hg.1.1 (show j.val < i.val from h1), one_apply_ne (fun e => by rw [e] at h1; omega)]

theorem apply_mul_inv_apply_eq_zero_of_normalizes {ρ κ : ℕ} (M : GL (Fin n) k) (hM : ∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ) :
    ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j →
      (M : Matrix (Fin n) (Fin n) k) i p * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) q j = 0 := by
  intro p q hpq i j hij
  have hne : p ≠ q := fun e => by rw [e] at hpq; exact lt_irrefl _ hpq.1
  have h := unipSym_entry (hM _ (elemU_mem hpq hne 1)) hij
  rw [conj_elemU_apply, mul_one] at h
  simpa using h

def esum (ρ κ : ℕ) (a : Fin n → Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) (p q : Fin n) : k :=
  ∑ i, ∑ j, if symEdge ρ κ i j then a i j * (X i p * Y q j) else 0

theorem edgeVal_conj {ρ κ : ℕ} (a : Fin n → Fin n → k) (M : GL (Fin n) k) (p q : Fin n) (hpq : p ≠ q) (s : k) :
    edgeVal ρ κ a (M * elemU p q hpq s * M⁻¹) =
      s * esum ρ κ a (M : Matrix (Fin n) (Fin n) k) ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q := by
  unfold edgeVal esum
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with he
  · have hij : i ≠ j := fun e => by unfold symEdge at he; rw [e] at he; omega
    rw [conj_elemU_apply, one_apply_ne hij, zero_add]; ring
  · rw [mul_zero]

theorem esum_single {ρ κ : ℕ} (a : Fin n → Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) (p q i0 j0 : Fin n)
    (hz : ∀ i j : Fin n, symEdge ρ κ i j → X i p * Y q j ≠ 0 → i = i0 ∧ j = j0) :
    esum ρ κ a X Y p q = if symEdge ρ κ i0 j0 then a i0 j0 * (X i0 p * Y q j0) else 0 := by
  unfold esum
  rw [Finset.sum_eq_single i0, Finset.sum_eq_single j0]
  · intro j _ hj
    split_ifs with he
    · rcases eq_or_ne (X i0 p * Y q j) 0 with h | h
      · rw [h, mul_zero]
      · exact absurd (hz _ _ he h).2 hj
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with he
    · rcases eq_or_ne (X i p * Y q j) 0 with h | h
      · rw [h, mul_zero]
      · exact absurd (hz _ _ he h).1 hi
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem char_cancel (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {A B : k} (h : ∀ s : k, ψ (s * A) = ψ (s * B)) : A = B := by
  by_contra hne
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 hψ
  have hAB : A - B ≠ 0 := sub_ne_zero.2 hne
  have e : x / (A - B) * A = x / (A - B) * B + x := by field_simp; ring
  have h1 := h (x / (A - B))
  rw [e, AddChar.map_add_eq_mul] at h1
  have h0 : ψ (x / (A - B) * B) ≠ 0 := fun h0 => by
    have := AddChar.map_add_eq_mul ψ (x / (A - B) * B) (-(x / (A - B) * B))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  exact hx (mul_left_cancel₀ h0 (by rw [mul_one]; exact h1))

theorem hC_of {ρ κ : ℕ} (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : Fin n → Fin n → k) (M : GL (Fin n) k)
    (hM : ∀ h ∈ unipSym k n ρ κ, ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h))
    (p q : Fin n) (hpq : Prec ρ κ p q) :
    esum ρ κ a (M : Matrix (Fin n) (Fin n) k) ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      if symEdge ρ κ p q then a p q else 0 := by
  have hne : p ≠ q := fun e => by rw [e] at hpq; exact lt_irrefl _ hpq.1
  have e1 : ∀ s, edgeVal ρ κ a (elemU p q hne s) = s * esum ρ κ a 1 1 p q := fun s => by
    have := edgeVal_conj (ρ := ρ) (κ := κ) a (1 : GL (Fin n) k) p q hne s
    rwa [one_mul, inv_one, mul_one, Units.val_one] at this
  have key : esum ρ κ a (M : Matrix (Fin n) (Fin n) k) ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      esum ρ κ a 1 1 p q := char_cancel ψ hψ fun s => by
    rw [← edgeVal_conj (ρ := ρ) (κ := κ) a M p q hne s, ← e1]; exact hM _ (elemU_mem hpq hne s)
  rw [key, esum_single a 1 1 p q p q]
  · simp
  · intro i j _ h
    constructor
    · by_contra hc; apply h; rw [one_apply_ne hc, zero_mul]
    · by_contra hc; apply h; rw [one_apply_ne (Ne.symm hc), mul_zero]

end Conj

theorem normaliser_unipSym_char : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → 2 ≤ κ →
    ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) →
    ∀ M : GL (Fin n) k, (∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ ∧
      ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h)) →
    (∀ h ∈ unipSym k n ρ κ, M⁻¹ * h * M ∈ unipSym k n ρ κ) →
    ∃ s c : kˣ, ∃ h ∈ unipSym k n ρ κ,
      (M : Matrix (Fin n) (Fin n) k) = midDiag n ρ κ (s : k) (c : k) * (h : Matrix (Fin n) (Fin n) k) := by
  intro k _ n ρ κ hn hρ hκ ψ hψ a ha M hM hM'
  have hXY : (M : Matrix (Fin n) (Fin n) k) * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYX : ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hP := apply_mul_inv_apply_eq_zero_of_normalizes M (fun h hh => (hM h hh).1)
  have hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j →
      ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i p * (M : Matrix (Fin n) (Fin n) k) q j = 0 := by
    have := apply_mul_inv_apply_eq_zero_of_normalizes M⁻¹ (fun h hh => by rw [inv_inv]; exact hM' h hh)
    simpa only [inv_inv] using this
  have hC := hC_of ψ hψ a M (fun h hh => (hM h hh).2)
  obtain ⟨X, hX⟩ : ∃ X, X = (M : Matrix (Fin n) (Fin n) k) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := ⟨_, rfl⟩
  rw [← hX, ← hY] at hXY hYX hP hP' hC
  rw [← hX]
  have patX := pattern hn hρ hκ hXY hYX hP hP'
  have patY := pattern hn hρ hκ hYX hXY hP' hP
  have diag : ∀ b : Fin n, X b b * Y b b = 1 := by
    intro b
    have h := congrFun (congrFun hXY b) b
    rw [mul_apply, Finset.sum_eq_single b, one_apply_eq] at h
    · exact h
    · intro j _ hj
      rcases eq_or_ne (X b j) 0 with h1 | h1
      · rw [h1, zero_mul]
      rcases eq_or_ne (Y j b) 0 with h2 | h2
      · rw [h2, mul_zero]
      exfalso
      have e1 := patX b j h1
      have e2 := patY j b h2
      have : j.val ≠ b.val := fun e => hj (Fin.ext e)
      unfold Prec at e1 e2; omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have hX0 : ∀ b, X b b ≠ 0 := fun b => left_ne_zero_of_mul_eq_one (diag b)
  have hY0 : ∀ b, Y b b ≠ 0 := fun b => right_ne_zero_of_mul_eq_one (diag b)
  obtain ⟨tF, htF⟩ : ∃ x : Fin n, x.val = ρ + κ := ⟨⟨ρ + κ, by omega⟩, rfl⟩
  obtain ⟨tmF, htmF⟩ : ∃ x : Fin n, x.val = ρ + κ - 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨tpF, htpF⟩ : ∃ x : Fin n, x.val = ρ + κ + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨rF, hrF⟩ : ∃ x : Fin n, x.val = ρ := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨rmF, hrmF⟩ : ∃ x : Fin n, x.val = ρ - 1 := ⟨⟨_, by omega⟩, rfl⟩

  have S1 : X tF tmF = 0 := by
    have h := hC tmF tpF (by unfold Prec; omega)
    rw [esum_single a X Y tmF tpF tF tpF (fun i j he hne => by
      have e1 := patX i tmF (left_ne_zero_of_mul hne)
      have e2 := patY tpF j (right_ne_zero_of_mul hne)
      unfold symEdge at he; unfold Prec at e1 e2
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩),
      if_pos (by unfold symEdge; omega), if_neg (by unfold symEdge; omega)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (ha _ _ (by unfold symEdge; omega))
    · exact (mul_eq_zero.1 h).resolve_right (hY0 tpF)

  have S2 : Y rF tF = 0 := by
    have h := hC rmF rF (by unfold Prec; omega)
    rw [esum_single a X Y rmF rF rmF tF (fun i j he hne => by
      have e1 := patX i rmF (left_ne_zero_of_mul hne)
      have e2 := patY rF j (right_ne_zero_of_mul hne)
      unfold symEdge at he; unfold Prec at e1 e2
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩),
      if_pos (by unfold symEdge; omega), if_neg (by unfold symEdge; omega)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (ha _ _ (by unfold symEdge; omega))
    · exact (mul_eq_zero.1 h).resolve_left (hX0 rmF)
  have S3 : Y tF tmF = 0 := by
    have h := congrFun (congrFun hYX tF) tmF
    rw [mul_apply, Finset.sum_eq_single tmF, one_apply_ne (fun e => by rw [e] at htF; omega)] at h
    · exact (mul_eq_zero.1 h).resolve_right (hX0 tmF)
    · intro j _ hj
      rcases eq_or_ne (Y tF j) 0 with h1 | h1
      · rw [h1, zero_mul]
      rcases eq_or_ne (X j tmF) 0 with h2 | h2
      · rw [h2, mul_zero]
      exfalso
      by_cases hjt : j = tF
      · rw [hjt] at h2; exact h2 S1
      have e1 := patY tF j h1
      have e2 := patX j tmF h2
      have : j.val ≠ tmF.val := fun e => hj (Fin.ext e)
      have : j.val ≠ tF.val := fun e => hjt (Fin.ext e)
      unfold Prec at e1 e2; omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have S4 : X rF tF = 0 := by
    have h := congrFun (congrFun hXY rF) tF
    rw [mul_apply, Finset.sum_eq_single tF, one_apply_ne (fun e => by rw [e] at hrF; omega)] at h
    · exact (mul_eq_zero.1 h).resolve_right (hY0 tF)
    · intro j _ hj
      rcases eq_or_ne (X rF j) 0 with h1 | h1
      · rw [h1, zero_mul]
      rcases eq_or_ne (Y j tF) 0 with h2 | h2
      · rw [h2, mul_zero]
      exfalso
      by_cases hjr : j = rF
      · rw [hjr] at h2; exact h2 S2
      have e1 := patX rF j h1
      have e2 := patY j tF h2
      have : j.val ≠ tF.val := fun e => hj (Fin.ext e)
      have : j.val ≠ rF.val := fun e => hjr (Fin.ext e)
      unfold Prec at e1 e2; omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have patX' : ∀ i b : Fin n, X i b ≠ 0 → i.val = b.val ∨ Prec ρ κ i b := by
    intro i b h
    rcases patX i b h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; apply h
      rw [show i = rF from Fin.ext (by omega), show b = tF from Fin.ext (by omega)]; exact S4
    · exfalso; apply h
      rw [show i = tF from Fin.ext (by omega), show b = tmF from Fin.ext (by omega)]; exact S1
  have patY' : ∀ i b : Fin n, Y i b ≠ 0 → i.val = b.val ∨ Prec ρ κ i b := by
    intro i b h
    rcases patY i b h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; apply h
      rw [show i = rF from Fin.ext (by omega), show b = tF from Fin.ext (by omega)]; exact S2
    · exfalso; apply h
      rw [show i = tF from Fin.ext (by omega), show b = tmF from Fin.ext (by omega)]; exact S3

  have S5 : ∀ p q : Fin n, symEdge ρ κ p q → X p p = X q q := by
    intro p q he
    have hpq : Prec ρ κ p q := by unfold symEdge at he; unfold Prec; omega
    have h := hC p q hpq
    rw [esum_single a X Y p q p q (fun i j he' hne => by
      have e1 := patX' i p (left_ne_zero_of_mul hne)
      have e2 := patY' q j (right_ne_zero_of_mul hne)
      unfold symEdge at he he'; unfold Prec at e1 e2 hpq
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩), if_pos he, if_pos he] at h
    have h1 : X p p * Y q q = 1 := mul_left_cancel₀ (ha p q he) (by rw [mul_one]; exact h)
    exact mul_right_cancel₀ (hY0 q) (by rw [h1, diag q])
  let D : ℕ → k := fun m => if h : m < n then X ⟨m, h⟩ ⟨m, h⟩ else 0
  have hDX : ∀ i : Fin n, X i i = D i.val := fun i => by simp [D, i.2]
  have hD : ∀ m m' (hm : m < n) (hm' : m' < n),
      ((m' = m + 1 ∧ m + 1 ≠ ρ ∧ m + 1 ≠ ρ + κ) ∨ (m + 1 = ρ ∧ m' = ρ + κ)) → D m = D m' := by
    intro m m' hm hm' he
    have := S5 ⟨m, hm⟩ ⟨m', hm'⟩ he
    simpa [D, hm, hm'] using this
  have c1 : ∀ m, m < ρ → D m = D 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih (by omega)]
      exact (hD m (m + 1) (by omega) (by omega) (Or.inl ⟨rfl, by omega, by omega⟩)).symm
  have c2 : D (ρ + κ) = D 0 := by
    rw [← c1 (ρ - 1) (by omega)]
    exact (hD (ρ - 1) (ρ + κ) (by omega) (by omega) (Or.inr ⟨by omega, rfl⟩)).symm
  have c3 : ∀ m, ρ + κ + m < n → D (ρ + κ + m) = D 0 := by
    intro m hm
    induction m with
    | zero => exact c2
    | succ m ih =>
      rw [← ih (by omega)]
      exact (hD (ρ + κ + m) (ρ + κ + (m + 1)) (by omega) (by omega) (Or.inl ⟨by omega, by omega, by omega⟩)).symm
  have c4 : ∀ m, m < κ → D (ρ + m) = D ρ := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih (by omega)]
      exact (hD (ρ + m) (ρ + (m + 1)) (by omega) (by omega) (Or.inl ⟨by omega, by omega, by omega⟩)).symm
  have diagX : ∀ i : Fin n, X i i = if ρ ≤ i.val ∧ i.val < ρ + κ then D ρ else D 0 := by
    intro i
    rw [hDX]
    split_ifs with hi
    · have := c4 (i.val - ρ) (by omega); rwa [show ρ + (i.val - ρ) = i.val by omega] at this
    · by_cases h1 : i.val < ρ
      · exact c1 _ h1
      · have := c3 (i.val - (ρ + κ)) (by omega)
        rwa [show ρ + κ + (i.val - (ρ + κ)) = i.val by omega] at this
  have hs0 : D 0 ≠ 0 := by have := hX0 ⟨0, by omega⟩; rwa [hDX] at this
  have hc0 : D ρ ≠ 0 := by have := hX0 ⟨ρ, by omega⟩; rwa [hDX] at this
  have hDD : midDiag n ρ κ (D 0) (D ρ) * midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ = 1 := by
    unfold midDiag; rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> field_simp
  have hD'D : midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * midDiag n ρ κ (D 0) (D ρ) = 1 := by
    unfold midDiag; rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> field_simp
  have hmd : ∀ (s c : k) (Z : Matrix (Fin n) (Fin n) k) (i j : Fin n),
      (midDiag n ρ κ s c * Z) i j = (if ρ ≤ i.val ∧ i.val < ρ + κ then c else s) * Z i j := by
    intro s c Z i j; unfold midDiag; rw [diagonal_mul]
  let U : GL (Fin n) k := ⟨midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X, Y * midDiag n ρ κ (D 0) (D ρ),
    by rw [mul_assoc, ← mul_assoc X, hXY, one_mul, hD'D],
    by rw [mul_assoc, ← mul_assoc (midDiag n ρ κ (D 0) (D ρ)), hDD, one_mul, hYX]⟩
  refine ⟨Units.mk0 (D 0) hs0, Units.mk0 (D ρ) hc0, U, ?_, ?_⟩
  · refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      show (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X) i j = 0
      rw [hmd]
      rcases eq_or_ne (X i j) 0 with h | h
      · rw [h, mul_zero]
      · exfalso; have := patX' i j h; unfold Prec at this; omega
    · show (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X) i i = 1
      rw [hmd, diagX]
      split_ifs with hi
      · exact inv_mul_cancel₀ hc0
      · exact inv_mul_cancel₀ hs0
    · show (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X) i j = 0
      rw [hmd]
      rcases eq_or_ne (X i j) 0 with h | h
      · rw [h, mul_zero]
      · exfalso; have := patX' i j h; unfold Prec at this; omega
  · show X = midDiag n ρ κ (D 0) (D ρ) * (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X)
    rw [← mul_assoc, hDD, one_mul]

end GlobalTheory.SymNorm

end
