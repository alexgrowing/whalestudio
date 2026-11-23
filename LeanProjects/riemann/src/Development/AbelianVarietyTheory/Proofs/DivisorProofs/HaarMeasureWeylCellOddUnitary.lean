import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell GlobalTheory.LGrp GlobalTheory.BorelUMod

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

namespace Volume

section Block

variable {L : Type} [Field L] {n m : ℕ}

def incl (L : Type) [Field L] (e : Fin m ↪ Fin n) : Matrix (Fin n) (Fin m) L := fun i a => if i = e a then 1 else 0

def extZero (e : Fin m ↪ Fin n) (X : Matrix (Fin m) (Fin m) L) : Matrix (Fin n) (Fin n) L :=
  incl L e * X * (incl L e).transpose

theorem extZero_apply (e : Fin m ↪ Fin n) (X : Matrix (Fin m) (Fin m) L) (a b : Fin m) :
    extZero e X (e a) (e b) = X a b := by
  simp [extZero, incl, Matrix.mul_apply, e.injective.eq_iff]

theorem extZero_row (e : Fin m ↪ Fin n) (X : Matrix (Fin m) (Fin m) L) {i : Fin n} (hi : ∀ a, i ≠ e a) (j : Fin n) :
    extZero e X i j = 0 := by
  simp [extZero, incl, Matrix.mul_apply, hi]

theorem extZero_col (e : Fin m ↪ Fin n) (X : Matrix (Fin m) (Fin m) L) (i : Fin n) {j : Fin n} (hj : ∀ a, j ≠ e a) :
    extZero e X i j = 0 := by
  simp [extZero, incl, Matrix.mul_apply, hj]

theorem transpose_incl_mul (e : Fin m ↪ Fin n) : (incl L e).transpose * incl L e = 1 := by
  ext a b
  simp [incl, Matrix.mul_apply, Matrix.one_apply, e.injective.eq_iff, eq_comm]

theorem extZero_mul (e : Fin m ↪ Fin n) (X Y : Matrix (Fin m) (Fin m) L) :
    extZero e X * extZero e Y = extZero e (X * Y) := by
  unfold extZero
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incl L e).transpose, transpose_incl_mul, Matrix.one_mul]

theorem extZero_add (e : Fin m ↪ Fin n) (X Y : Matrix (Fin m) (Fin m) L) :
    extZero e (X + Y) = extZero e X + extZero e Y := by
  unfold extZero
  rw [Matrix.mul_add, Matrix.add_mul]

def blockHom (e : Fin m ↪ Fin n) : Matrix (Fin m) (Fin m) L →* Matrix (Fin n) (Fin n) L where
  toFun g := 1 + extZero e (g - 1)
  map_one' := by simp [extZero]
  map_mul' g h := by
    have : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
    rw [this, extZero_add, extZero_add, ← extZero_mul]
    noncomm_ring

theorem blockHom_apply (e : Fin m ↪ Fin n) (g : Matrix (Fin m) (Fin m) L) (a b : Fin m) :
    blockHom e g (e a) (e b) = g a b := by
  show (1 + extZero e (g - 1) : Matrix (Fin n) (Fin n) L) (e a) (e b) = _
  simp [extZero_apply, Matrix.one_apply, e.injective.eq_iff]

theorem blockHom_out (e : Fin m ↪ Fin n) (g : Matrix (Fin m) (Fin m) L) {i j : Fin n}
    (h : (∀ a, i ≠ e a) ∨ ∀ a, j ≠ e a) : blockHom e g i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  show (1 + extZero e (g - 1) : Matrix (Fin n) (Fin n) L) i j = _
  rcases h with h | h
  · rw [Matrix.add_apply, extZero_row e _ h, add_zero]
  · rw [Matrix.add_apply, extZero_col e _ _ h, add_zero]

theorem cases_range (e : Fin m ↪ Fin n) (i j : Fin n) :
    (∃ a b, i = e a ∧ j = e b) ∨ (∀ a, i ≠ e a) ∨ ∀ a, j ≠ e a := by
  by_contra h
  push_neg at h
  obtain ⟨h1, ⟨a, ha⟩, b, hb⟩ := h
  exact h1 a b ha hb

theorem blockHom_injective (e : Fin m ↪ Fin n) : Function.Injective (blockHom (L := L) e) := fun g h hgh => by
  ext a b
  rw [← blockHom_apply e g, hgh, blockHom_apply]

theorem blockHom_submatrix (e : Fin m ↪ Fin n) (M : Matrix (Fin n) (Fin n) L)
    (hM : ∀ i j, ((∀ a, i ≠ e a) ∨ ∀ a, j ≠ e a) → M i j = (1 : Matrix (Fin n) (Fin n) L) i j) :
    blockHom e (M.submatrix e e) = M := by
  ext i j
  rcases cases_range e i j with ⟨a, b, rfl, rfl⟩ | h
  · rw [blockHom_apply]; rfl
  · rw [blockHom_out e _ h, hM i j h]

theorem adjJ_blockHom (σ : L →+* L) (e : Fin m ↪ Fin n) (he : ∀ a, (e a).rev = e a.rev) (g : Matrix (Fin m) (Fin m) L) :
    adjJ σ (blockHom e g) = blockHom e (adjJ σ g) := by
  ext i j
  rcases cases_range e i j with ⟨a, b, rfl, rfl⟩ | h
  · rw [blockHom_apply]
    simp only [adjJ, he, blockHom_apply]
  · have h' : (∀ a, j.rev ≠ e a) ∨ ∀ a, i.rev ≠ e a := by
      refine h.symm.imp (fun h a ha => h a.rev ?_) (fun h a ha => h a.rev ?_) <;> rw [← he, ← ha, Fin.rev_rev]
    rw [blockHom_out e _ h, ← adjJ_one σ]
    simp only [adjJ]
    rw [blockHom_out e _ h']

def three (A : Fin n) (hA : A.rev.val = A.val + 2) : Fin 3 ↪ Fin n :=
  ⟨fun a => ⟨A.val + a.val, by have := A.rev.2; have := a.2; omega⟩, fun a b h => by
    have := congrArg Fin.val h
    exact Fin.ext (by simpa using this)⟩

theorem three_val (A : Fin n) (hA : A.rev.val = A.val + 2) (a : Fin 3) : (three A hA a).val = A.val + a.val := rfl

theorem three_rev (A : Fin n) (hA : A.rev.val = A.val + 2) (a : Fin 3) : (three A hA a).rev = three A hA a.rev := by
  have := a.2
  have := A.2
  rw [Fin.val_rev] at hA
  ext
  simp only [Fin.val_rev, three_val]
  omega

theorem three_zero (A : Fin n) (hA : A.rev.val = A.val + 2) : three A hA 0 = A := Fin.ext rfl

theorem three_two (A : Fin n) (hA : A.rev.val = A.val + 2) : three A hA 2 = A.rev := Fin.ext hA.symm

theorem three_out (A : Fin n) (hA : A.rev.val = A.val + 2) (i : Fin n) :
    (∀ a, i ≠ three A hA a) ↔ (i < A ∨ A.rev < i) := by
  simp only [Fin.lt_def, ne_eq, Fin.ext_iff, three_val, Fin.forall_fin_succ, hA]
  simp
  omega

end Block

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def blockU (σ : L →+* L) (A : Fin n) (hA : A.rev.val = A.val + 2) : (borelU σ 3).U →* GU σ n :=
  ((Units.map (blockHom (three A hA))).comp ((GU σ 3).subtype.comp (borelU σ 3).U.subtype)).codRestrict (GU σ n)
    fun u => by
      rw [mem_GU_iff_adjJ]
      show blockHom (three A hA) (u.1.1⁻¹).val = adjJ σ (blockHom (three A hA) u.1.1.val)
      rw [adjJ_blockHom σ _ (three_rev A hA), (mem_GU_iff_adjJ σ _).1 u.1.2]

theorem blockU_val (σ : L →+* L) (A : Fin n) (hA : A.rev.val = A.val + 2) (u : (borelU σ 3).U) :
    ((blockU σ A hA u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = blockHom (three A hA) u.1.1.val := rfl

theorem blockU_injective (σ : L →+* L) (A : Fin n) (hA : A.rev.val = A.val + 2) :
    Function.Injective (blockU σ A hA) := fun u w h =>
  Subtype.ext (Subtype.ext (Units.ext (blockHom_injective (three A hA)
    (by rw [← blockU_val, ← blockU_val, h]))))

def InBlock {σ : L →+* L} (A : Fin n) (u : GU σ n) : Prop :=
  IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < A ∨ A.rev < j) → ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0

theorem inBlock_blockU (σ : L →+* L) (A : Fin n) (hA : A.rev.val = A.val + 2) (u : (borelU σ 3).U) :
    InBlock A (blockU σ A hA u) := by
  obtain ⟨h1, h2⟩ := (mem_borelU_U σ 3 _).1 u.2
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij h => ?_⟩
  · rw [blockU_val]
    rcases cases_range (three A hA) i j with ⟨a, b, rfl, rfl⟩ | h
    · rw [blockHom_apply]
      refine h1 a b ?_
      rw [Fin.lt_def] at hij ⊢
      rw [three_val, three_val] at hij
      omega
    · rw [blockHom_out _ _ h, Matrix.one_apply_ne hij.ne']
  · rw [blockU_val]
    by_cases h : ∀ a, i ≠ three A hA a
    · rw [blockHom_out _ _ (Or.inl h), Matrix.one_apply_eq]
    · push_neg at h
      obtain ⟨a, rfl⟩ := h
      rw [blockHom_apply]
      exact h2 a
  · rw [blockU_val, blockHom_out _ _ (h.imp (fun h => (three_out A hA i).2 (Or.inl h))
      fun h => (three_out A hA j).2 (Or.inr h)), Matrix.one_apply_ne hij.ne]

theorem InBlock.out {σ : L →+* L} {A : Fin n} (hA : A.rev.val = A.val + 2) {u : GU σ n} (hu : InBlock A u) (i j : Fin n)
    (h : (∀ a, i ≠ three A hA a) ∨ ∀ a, j ≠ three A hA a) :
    ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  rw [three_out, three_out] at h
  rcases lt_trichotomy i j with e | rfl | e
  · rw [Matrix.one_apply_ne e.ne]
    refine hu.2 i j e ?_
    rcases h with (h | h) | h | h
    exacts [Or.inl h, Or.inr (h.trans e), Or.inl (e.trans h), Or.inr h]
  · rw [Matrix.one_apply_eq, hu.1.2]
  · rw [Matrix.one_apply_ne e.ne', hu.1.1 i j e]

theorem exists_blockU {σ : L →+* L} {A : Fin n} (hA : A.rev.val = A.val + 2) {u : GU σ n} (hu : InBlock A u) :
    ∃ w, blockU σ A hA w = u := by
  set e := three A hA with he
  have h1 := blockHom_submatrix e _ (hu.out hA)
  set X := (u.1.val).submatrix e e with hX
  have hinv := (mem_GU_iff_adjJ σ _).1 u.2
  have h2 : blockHom e (adjJ σ X) = (u.1⁻¹).val := by
    rw [← adjJ_blockHom σ e (three_rev A hA), h1, hinv]
  have h3 : X * adjJ σ X = 1 := blockHom_injective e (by rw [map_mul, map_one, h1, h2, Units.mul_inv])
  have h4 : adjJ σ X * X = 1 := blockHom_injective e (by rw [map_mul, map_one, h1, h2, Units.inv_mul])
  let g : GL (Fin 3) L := ⟨X, adjJ σ X, h3, h4⟩
  have hg : g ∈ GU σ 3 := (mem_GU_iff_adjJ σ g).2 rfl
  refine ⟨⟨⟨g, hg⟩, (mem_borelU_U σ 3 _).2 ⟨fun a b hab => hu.1.1 (e a) (e b) ?_, fun a => hu.1.2 (e a)⟩⟩,
    Subtype.ext (Units.ext h1)⟩
  rw [Fin.lt_def] at hab ⊢
  rw [he, three_val, three_val]
  omega

def wt (j : ℕ) : Fin 3 → Fin 3 → ℤ := fun a b => if a = 0 ∧ b = 2 then -(j : ℤ) else -((j / 2 : ℕ) : ℤ)

theorem isWeight_wt (j : ℕ) : IsWeight (wt j) := by
  refine ⟨fun a b => ?_, fun a b c h1 h2 => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [wt]
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [wt] at h1 h2 ⊢
    omega

theorem isIdealWeight_wt (j : ℕ) : IsIdealWeight (wt (j + 1)) (wt j) := by
  refine ⟨fun a b h => ?_, fun a b c h1 h2 => ?_, fun a b c h1 h2 => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [wt] at h ⊢ <;> omega
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [wt] at h1 h2 ⊢
    omega
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [wt] at h1 h2 ⊢
    omega

theorem sum_wt (j : ℕ) : ∑ p ∈ upPairs 3, (wt j p.1 p.2 - wt (j + 1) p.1 p.2).toNat + (j + 2 * (j / 2)) =
    j + 1 + 2 * ((j + 1) / 2) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_three, wt]
  omega

theorem le_exp_half {x : L} {j : ℕ} (h : Valued.v x * Valued.v x ≤ WithZero.exp (j : ℤ)) :
    Valued.v x ≤ WithZero.exp ((j / 2 : ℕ) : ℤ) := by
  by_cases h0 : x = 0
  · simp [h0]
  · rw [v_eq_exp h0] at h ⊢
    rw [← WithZero.exp_add, WithZero.exp_le_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem mem_unipLat_wt {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (j : ℕ) (w : (borelU σ 3).U) :
    w ∈ unipLat hσ (isWeight_wt j) ↔ Valued.v (w.1.1.val 0 2) ≤ WithZero.exp (j : ℤ) := by
  obtain ⟨h1, h2⟩ := (mem_borelU_U σ 3 _).1 w.2
  rw [mem_unipLat, mem_upLat]
  constructor
  · intro h
    simpa [wt] using h.2 0 2 (by decide)
  · intro h
    have hinv := (mem_GU_iff_adjJ σ _).1 w.1.2
    have hs : Valued.v (σ (w.1.1.val 0 2) + w.1.1.val 0 2) ≤ WithZero.exp (j : ℤ) :=
      Valuation.map_add_le _ (by rwa [hσ]) h
    have e1 : (w.1.1.val * adjJ σ w.1.1.val) 0 2 = 0 := by rw [← hinv, Units.mul_inv]; simp
    have e2 : (adjJ σ w.1.1.val * w.1.1.val) 0 2 = 0 := by rw [← hinv, Units.inv_mul]; simp
    simp only [Matrix.mul_apply, Fin.sum_univ_three, adjJ] at e1 e2
    have r0 : (0 : Fin 3).rev = 2 := rfl
    have r1 : (1 : Fin 3).rev = 1 := rfl
    have r2 : (2 : Fin 3).rev = 0 := rfl
    simp only [r0, r1, r2, h2, map_one, one_mul, mul_one] at e1 e2
    have b1 : Valued.v (w.1.1.val 0 1) ≤ WithZero.exp ((j / 2 : ℕ) : ℤ) := by
      refine le_exp_half ?_
      have : σ (w.1.1.val 0 2) + w.1.1.val 0 2 = -(w.1.1.val 0 1 * σ (w.1.1.val 0 1)) := by linear_combination e1
      rwa [this, Valuation.map_neg, map_mul, hσ] at hs
    have b2 : Valued.v (w.1.1.val 1 2) ≤ WithZero.exp ((j / 2 : ℕ) : ℤ) := by
      refine le_exp_half ?_
      have : σ (w.1.1.val 0 2) + w.1.1.val 0 2 = -(σ (w.1.1.val 1 2) * w.1.1.val 1 2) := by linear_combination e2
      rwa [this, Valuation.map_neg, map_mul, hσ] at hs
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · rcases hab.eq_or_lt with rfl | e
      · simp [h2]
      · simp [h1 a b e, Matrix.one_apply_ne e.ne']
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hab.ne, sub_zero]
      fin_cases a <;> fin_cases b <;> simp at hab
      · simpa [wt] using b1
      · simpa [wt] using h
      · simpa [wt] using b2

end Unitary

end Volume

open Volume in

theorem measure_shellU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ j : ℕ, μ (shellU k y j) = (q : ENNReal) ^ (j + 2 * (j / 2)) := by
  intro L _ _ _ ϖ σ q h n k hk hn y hyK hy _ _ μ _ hμ j
  have hA := val_rev_lo_of_last k hk hn
  have hC : ∀ u : GU σ n, u ∈ cellU y ↔ InBlock (lo k) u := mem_cellU_last_iff L ϖ σ q h n k hk hn y hyK hy
  let φ : (borelU σ 3).U →* cellU y :=
    (blockU σ (lo k) hA).codRestrict (cellU y) fun w => (hC _).2 (inBlock_blockU σ _ hA w)
  have hφ : Function.Injective φ := fun u w e => blockU_injective σ _ hA (congrArg Subtype.val e)
  have hc : ∀ w, cornerU k (φ w : GU σ n) = w.1.1.val 0 2 := fun w => by
    have := blockHom_apply (three (lo k) hA) w.1.1.val 0 2
    rwa [three_zero, three_two] at this
  let S : ℕ → Subgroup (cellU y) := fun j => (unipLat h.2.1 (isWeight_wt j)).map φ
  have hSe : ∀ j : ℕ, (S j : Set (cellU y)) = shellU k y j := fun j => by
    ext u
    obtain ⟨w, hw⟩ := exists_blockU hA ((hC _).1 u.2)
    obtain rfl : φ w = u := Subtype.ext hw
    show φ w ∈ S j ↔ Valued.v (cornerU k (φ w : GU σ n)) ≤ _
    rw [hc, ← mem_unipLat_wt h.2.1]
    exact Subgroup.mem_map_iff_mem hφ
  have hS0 : S 0 = (KU σ n).subgroupOf (cellU y) := by
    ext u
    rw [Subgroup.mem_subgroupOf, GlobalTheory.SatakeWeyl.mem_KU_iff h.2.1]
    constructor
    · rintro ⟨w, hw, rfl⟩ i j
      show blockHom (three (lo k) hA) w.1.1.val i j ∈ intL L
      have h1 : ∀ {m : ℕ} (a b : Fin m), (1 : Matrix (Fin m) (Fin m) L) a b ∈ intL L := fun a b => by
        rw [Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      rcases cases_range (three (lo k) hA) i j with ⟨a, b, rfl, rfl⟩ | e
      · rw [blockHom_apply, ← sub_add_cancel (w.1.1.val a b) ((1 : Matrix (Fin 3) (Fin 3) L) a b)]
        refine add_mem ?_ (h1 a b)
        rcases le_or_gt b a with e | e
        · rw [← Matrix.sub_apply, hw.1 a b e]
          exact zero_mem _
        · have := hw.2 a b e
          have e0 : wt 0 a b = 0 := by simp [wt]
          rwa [e0] at this
      · rw [blockHom_out _ _ e]
        exact h1 i j
    · intro hu
      rw [← SetLike.mem_coe, hSe]
      exact hu _ _
  have hS : ∀ j : ℕ, IsOpen (S j : Set (cellU y)) := fun j => by
    refine Subgroup.isOpen_mono (H₁ := S 0) (fun u hu => ?_) ?_
    · rw [← SetLike.mem_coe, hSe] at hu ⊢
      exact shellU_mono k y (by omega) hu
    · rw [hS0]
      exact (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h).1.preimage continuous_subtype_val
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  induction j with
  | zero => rw [← hSe, hS0, hμ]; simp
  | succ j ih =>
    have e : (S j).relIndex (S (j + 1)) = _ :=
      (Subgroup.relIndex_map_map_of_injective _ _ hφ).trans
        (relIndex_unipLat h (isWeight_wt (j + 1)) (isWeight_wt j) (isIdealWeight_wt j))
    haveI : ((S j).subgroupOf (S (j + 1))).FiniteIndex := ⟨ne_of_eq_of_ne e (pow_ne_zero _ hq)⟩
    have := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (S j) (S (j + 1))
      (Subgroup.map_mono fun _ hu => upLat_mono (isIdealWeight_wt j).1 hu)
      (hS j).measurableSet μ
    rw [← hSe, ← this, hSe, ih, e, Nat.cast_pow, ← pow_add, sum_wt]

end WeylUnipotentShell

end WeylCell

end GlobalTheory
