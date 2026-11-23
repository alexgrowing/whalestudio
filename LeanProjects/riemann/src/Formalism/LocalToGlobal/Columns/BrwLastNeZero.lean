import Mathlib
import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLattices.TraceIntegrality

section Sums

variable {κ : ℕ}

theorem brw_last_ne_zero (hκ : 1 ≤ κ) : (Fin.last κ : Fin (κ + 1)) ≠ 0 := by
  intro e
  have := congrArg Fin.val e
  simp at this
  omega

theorem brw_sum_le (hκ : 1 ≤ κ) (f : Fin (κ + 1) → ℝ) (c : ℝ) (h : ∀ i, i ≠ 0 → i ≠ Fin.last κ → f i ≤ c) :
    ∑ i, f i ≤ f 0 + f (Fin.last κ) + ((κ : ℝ) - 1) * c := by
  classical
  have h0 := brw_last_ne_zero hκ
  have e1 : ∑ i, f i = f 0 + ∑ i ∈ Finset.univ.erase (0 : Fin (κ + 1)), f i :=
    (Finset.add_sum_erase _ f (Finset.mem_univ 0)).symm
  have e2 : ∑ i ∈ Finset.univ.erase (0 : Fin (κ + 1)), f i =
      f (Fin.last κ) + ∑ i ∈ (Finset.univ.erase (0 : Fin (κ + 1))).erase (Fin.last κ), f i :=
    (Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨h0, Finset.mem_univ _⟩)).symm
  have e3 : ∑ i ∈ (Finset.univ.erase (0 : Fin (κ + 1))).erase (Fin.last κ), f i ≤
      ((Finset.univ.erase (0 : Fin (κ + 1))).erase (Fin.last κ)).card • c :=
    Finset.sum_le_card_nsmul _ _ _ fun i hi =>
      h i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1
  have e4 : ((Finset.univ.erase (0 : Fin (κ + 1))).erase (Fin.last κ)).card = κ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h0, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  rw [e4, nsmul_eq_mul, Nat.cast_sub hκ] at e3
  push_cast at e3
  rw [e1, e2]
  linarith

theorem brw_wt_cast (lam : Fin (κ + 1) → ℤ) : (wt lam : ℝ) = ∑ i, (lam i : ℝ) := by
  unfold wt
  push_cast
  rfl

theorem brw_wt_plus (lam : Fin (κ + 1) → ℤ) :
    (wt (plus lam) : ℝ) = (wt lam : ℝ) - ((κ : ℝ) + 1) * (lam (Fin.last κ) : ℝ) := by
  rw [brw_wt_cast, brw_wt_cast]
  unfold plus
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Sums

section Shape

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def kIdx (i : Fin (kap R + 1)) : Fin R.k := Fin.cast (kap_succ_k R) i

theorem lamZ_eq_hc (u : Pr.Word) (τ : X.Tau) (i : Fin (kap R + 1)) :
    (lamZ W u τ i : ℝ) = (((W.hc u τ).u (kIdx i) : ℚ) : ℝ) - ((R.k : ℝ) - 1) / 2 + (i.1 : ℝ) := by
  have hi : i.1 < R.k := lt_of_lt_of_eq i.2 (kap_succ_k R)
  have h1 : ((lamZ W u τ i : ℤ) : ℚ) = (W.hc u τ).u (kIdx i) - (((R.k : ℚ) - 1) / 2 - (i.1 : ℚ)) := by
    unfold lamZ castW
    rw [Wts.lamTrue_zero, Wts.lamN_eq W u (Nat.zero_le _) τ]
    have hi' : (Fin.cast (kap_succ R) i).1 < R.k := hi
    rw [dif_pos hi']
    rfl
  have h2 : (((lamZ W u τ i : ℤ) : ℚ) : ℝ) =
      (((W.hc u τ).u (kIdx i) - (((R.k : ℚ) - 1) / 2 - (i.1 : ℚ)) : ℚ) : ℝ) := by rw [h1]
  push_cast at h2
  rw [h2]
  ring

def kFirst (R : Ranks) : Fin R.k := ⟨0, by have := R.m_add_three_le_k; omega⟩

def kLast (R : Ranks) : Fin R.k := ⟨R.k - 1, by have := R.m_add_three_le_k; omega⟩

theorem brw_kap_cast' (R : Ranks) : (kap R : ℝ) = (R.k : ℝ) - 1 := by
  have := kap_cast R
  linarith

theorem aTop_eq_hc (u : Pr.Word) (τ : X.Tau) :
    (((W.hc u τ).u (kFirst R) : ℚ) : ℝ) = (W.aTop u τ : ℝ) + ((R.k : ℝ) - 1) / 2 := by
  have h := lamZ_eq_hc W u τ 0
  rw [lamZ_zero] at h
  have e : kIdx (0 : Fin (kap R + 1)) = kFirst R := rfl
  rw [e] at h
  simp only [Fin.val_zero, Nat.cast_zero] at h
  linarith

theorem bTop_eq_hc (u : Pr.Word) (τ : X.Tau) :
    (((W.hc u τ).u (kLast R) : ℚ) : ℝ) = -(W.bTop u τ : ℝ) - ((R.k : ℝ) - 1) / 2 := by
  have h := lamZ_eq_hc W u τ (Fin.last (kap R))
  rw [lamZ_last] at h
  have e : kIdx (Fin.last (kap R)) = kLast R := by
    apply Fin.ext
    show kap R = R.k - 1
    have := kap_succ_k R
    omega
  rw [e] at h
  simp only [Fin.val_last] at h
  rw [brw_kap_cast'] at h
  push_cast at h
  linarith

structure HCShape (u : Pr.Word) (a b' S : ℝ) : Prop where

  cloud : ∀ (τ : X.Tau) (i : Fin R.k), 0 < i.1 → i.1 < R.k - 1 →
    0 ≤ (((W.hc u τ).u i : ℚ) : ℝ) ∧ (((W.hc u τ).u i : ℚ) : ℝ) ≤ S

  top : ∀ τ ∈ W.tops, a ≤ (W.aTop u τ : ℝ) ∧ (W.aTop u τ : ℝ) ≤ 2 * a ∧ b' ≤ (W.bTop u τ : ℝ) ∧ (W.bTop u τ : ℝ) ≤ 2 * b'

  oth_last : ∀ τ, τ ∉ W.tops → -(1 / 2 : ℝ) ≤ (((W.hc u τ).u (kLast R) : ℚ) : ℝ)
  oth_first : ∀ τ, τ ∉ W.tops → (((W.hc u τ).u (kFirst R) : ℚ) : ℝ) ≤ 3 * S

  k_le : 4 * (R.k : ℝ) ≤ S
  kS_le : (R.k : ℝ) * S ≤ b'

structure HCCloud (u : Pr.Word) (S : ℝ) : Prop where
  v_cloud : ∀ τ, τ ∉ W.tops → ∀ i : Fin (R.k - 1), 0 ≤ (((W.hc u τ).v i : ℚ) : ℝ) ∧ (((W.hc u τ).v i : ℚ) : ℝ) ≤ S
  first : ∀ τ, τ ∉ W.tops → (((W.hc u τ).u (kFirst R) : ℚ) : ℝ) -
    (((W.hc u τ).v ⟨0, by have := R.m_add_three_le_k; omega⟩ : ℚ) : ℝ) ≤ 2 * S
  last : ∀ τ, τ ∉ W.tops → (((W.hc u τ).u (kLast R) : ℚ) : ℝ) =
    (((W.hc u τ).v ⟨R.k - 2, by have := R.m_add_three_le_k; omega⟩ : ℚ) : ℝ) - 1 / 2

variable {W}

theorem HCCloud.ext {u : Pr.Word} {S : ℝ} (h : HCCloud W u S) (τ : X.Tau) (hτ : τ ∉ W.tops) :
    -(1 / 2 : ℝ) ≤ (((W.hc u τ).u (kLast R) : ℚ) : ℝ) ∧ (((W.hc u τ).u (kFirst R) : ℚ) : ℝ) ≤ 3 * S := by
  constructor
  · rw [h.last τ hτ]
    have := (h.v_cloud τ hτ ⟨R.k - 2, by have := R.m_add_three_le_k; omega⟩).1
    linarith
  · have h1 := h.first τ hτ
    have h2 := (h.v_cloud τ hτ ⟨0, by have := R.m_add_three_le_k; omega⟩).2
    linarith

section Proofs

variable {u : Pr.Word} {a b' S : ℝ}

theorem brw_k_ge (R : Ranks) : (5 : ℝ) ≤ (R.k : ℝ) := by
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  exact_mod_cast (by omega : 5 ≤ R.k)

theorem brw_one_le_kap (R : Ranks) : 1 ≤ kap R := by
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  have h3 := kap_succ_k R
  omega

theorem HCShape.mid (h : HCShape W u a b' S) (τ : X.Tau) (i : Fin (kap R + 1)) (h0 : i ≠ 0) (h1 : i ≠ Fin.last (kap R)) :
    -((R.k : ℝ) / 2) ≤ (lamZ W u τ i : ℝ) ∧ (lamZ W u τ i : ℝ) ≤ S + (R.k : ℝ) / 2 - 3 / 2 := by
  have hk := kap_succ_k R
  have i0 : 0 < i.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
  have i1 : i.1 < kap R := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) fun e => h1 (Fin.ext e)
  have hc := h.cloud τ (kIdx i) i0 (by show i.1 < R.k - 1; omega)
  rw [lamZ_eq_hc]
  have c0 : (1 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast i0
  have c1 : (i.1 : ℝ) + 1 ≤ (kap R : ℝ) := by exact_mod_cast i1
  rw [brw_kap_cast'] at c1
  constructor <;> linarith [hc.1, hc.2]

theorem HCShape.c1 (h : HCShape W u a b' S) (τ : X.Tau) (hτ : τ ∈ W.tops) :
    (wt (lamZ W u τ) : ℝ) ≤ W.aTop u τ + (R.k : ℝ) * S := by
  rw [brw_wt_cast]
  have h1 := brw_sum_le (brw_one_le_kap R) (fun i => (lamZ W u τ i : ℝ)) (S + (R.k : ℝ) / 2 - 3 / 2)
    fun i h0 h1 => (h.mid τ i h0 h1).2
  simp only [lamZ_zero, lamZ_last] at h1
  rw [brw_kap_cast'] at h1
  push_cast at h1
  have hb := (h.top τ hτ).2.2.1
  have hk := brw_k_ge R
  have h4 := h.k_le
  have h5 := h.kS_le
  nlinarith

theorem HCShape.c2 (h : HCShape W u a b' S) (τ : X.Tau) (hτ : τ ∈ W.tops) :
    (wt (plus (lamZ W u τ)) : ℝ) ≤ W.aTop u τ + (R.k : ℝ) * (W.bTop u τ + S) := by
  rw [brw_wt_plus, lamZ_last, kap_cast]
  have := h.c1 τ hτ
  push_cast
  linarith

theorem HCShape.last_nonneg (h : HCShape W u a b' S) (τ : X.Tau) (hτ : τ ∉ W.tops) :
    ((R.k : ℝ) - 2) / 2 ≤ -(W.bTop u τ : ℝ) := by
  have h1 := h.oth_last τ hτ
  rw [bTop_eq_hc] at h1
  linarith

theorem HCShape.first_le (h : HCShape W u a b' S) (τ : X.Tau) (hτ : τ ∉ W.tops) :
    (W.aTop u τ : ℝ) ≤ 3 * S - ((R.k : ℝ) - 1) / 2 := by
  have h1 := h.oth_first τ hτ
  rw [aTop_eq_hc] at h1
  linarith

theorem HCShape.last_le (h : HCShape W u a b' S) (τ : X.Tau) : -(W.bTop u τ : ℝ) ≤ S + (R.k : ℝ) / 2 - 3 / 2 := by
  have hκ := brw_one_le_kap R
  have hk1 := R.m_add_three_le_k
  have hk2 := R.two_le_m
  have hk3 := kap_succ_k R
  let i : Fin (kap R + 1) := ⟨1, by omega⟩
  have i0 : i ≠ 0 := fun e => by have := congrArg Fin.val e; simp [i] at this
  have i1 : i ≠ Fin.last (kap R) := fun e => by
    have := congrArg Fin.val e
    simp [i] at this
    omega
  have h1 := (h.mid τ i i0 i1).2
  have h2 : lamZ W u τ (Fin.last (kap R)) ≤ lamZ W u τ i := lamZ_anti W u τ (Fin.le_last i)
  rw [lamZ_last] at h2
  have h3 : (-(W.bTop u τ : ℝ)) ≤ (lamZ W u τ i : ℝ) := by exact_mod_cast h2
  linarith

theorem HCShape.c3 (h : HCShape W u a b' S) (τ : X.Tau) (hτ : τ ∉ W.tops) :
    (wt (plus (lamZ W u τ)) : ℝ) ≤ ((R.k : ℝ) + 3) * S := by
  rw [brw_wt_cast]
  have hl := h.oth_last τ hτ
  have hmid : ∀ i : Fin (kap R + 1), i ≠ 0 → i ≠ Fin.last (kap R) → ((plus (lamZ W u τ) i : ℤ) : ℝ) ≤ S + 1 / 2 := by
    intro i h0 h1
    have hk := kap_succ_k R
    have i0 : 0 < i.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
    have i1 : i.1 < kap R := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) fun e => h1 (Fin.ext e)
    have hc := h.cloud τ (kIdx i) i0 (by show i.1 < R.k - 1; omega)
    have c1 : (i.1 : ℝ) + 1 ≤ (kap R : ℝ) := by exact_mod_cast i1
    rw [brw_kap_cast'] at c1
    unfold plus
    push_cast
    rw [lamZ_eq_hc, lamZ_last]
    rw [bTop_eq_hc] at hl
    push_cast
    linarith [hc.2]
  have h1 := brw_sum_le (brw_one_le_kap R) (fun i => ((plus (lamZ W u τ) i : ℤ) : ℝ)) (S + 1 / 2) hmid
  have e0 : ((plus (lamZ W u τ) 0 : ℤ) : ℝ) = (W.aTop u τ : ℝ) + (W.bTop u τ : ℝ) := by
    unfold plus
    rw [lamZ_zero, lamZ_last]
    push_cast
    ring
  have e1 : ((plus (lamZ W u τ) (Fin.last (kap R)) : ℤ) : ℝ) = 0 := by
    unfold plus
    simp
  simp only [e0, e1] at h1
  rw [brw_kap_cast'] at h1
  have f1 := h.first_le τ hτ
  have f2 := h.last_nonneg τ hτ
  have hk := brw_k_ge R
  have h4 := h.k_le
  nlinarith

theorem HCShape.c4 (h : HCShape W u a b' S) (τ : X.Tau) (hτ : τ ∉ W.tops) :
    (wt (lamZ W u τ) : ℝ) ≤ 2 * (R.k : ℝ) * S := by
  rw [brw_wt_cast]
  have h1 := brw_sum_le (brw_one_le_kap R) (fun i => (lamZ W u τ i : ℝ)) (S + (R.k : ℝ) / 2 - 3 / 2)
    fun i h0 h1 => (h.mid τ i h0 h1).2
  simp only [lamZ_zero, lamZ_last] at h1
  rw [brw_kap_cast'] at h1
  push_cast at h1
  have f1 := h.first_le τ hτ
  have f2 := h.last_le τ
  have hk := brw_k_ge R
  have h4 := h.k_le
  nlinarith

theorem wtWin_of_shape (h : HCShape W u a b' S) {C₀ : ℝ} (hC : 2 ≤ C₀) : WtWin W u C₀ a b' S where
  top := h.top
  top_wt := h.c1
  top_plus := h.c2
  oth_plus := h.c3
  oth_wt τ hτ := by
    have h1 := h.c4 τ hτ
    have hk := brw_k_ge R
    have h4 := h.k_le
    have : 0 ≤ (R.k : ℝ) * S := by nlinarith
    nlinarith
  oth_last τ hτ := by
    have f1 := h.last_nonneg τ hτ
    have f2 := h.last_le τ
    have hk := brw_k_ge R
    have h4 := h.k_le
    rw [abs_le]
    constructor <;> nlinarith

end Proofs

end Shape

section Inst

open Formalism.BasicNotions.Examples₂

def shapeU : Fin 8 → ℚ := ![1207/2, 47/2, 39/2, 31/2, 23/2, 15/2, 7/2, -519/2]

def shapeB : Fin 2 → ℚ := ![300, 320]

def shapeE : Fin 2 → ℚ := ![310, 330]

def shapeTop : HCParam R0 where
  u := shapeU
  v := hcV
  b := shapeB
  e := shapeE
  u_gt_v := by
    intro i
    fin_cases i <;> simp [shapeU, hcV] <;> norm_num
  v_gt_u := by
    intro i
    fin_cases i <;> simp [shapeU, hcV] <;> norm_num
  u_last_gt := by
    intro h h'
    simp [shapeU, shapeB, R0]
    norm_num
  gap_be := by
    intro j
    fin_cases j <;> simp [shapeB, shapeE, R0] <;> norm_num
  gap_eb := by
    intro j h
    fin_cases j
    · simp [shapeB, shapeE, R0]; norm_num
    · simp [R0] at h
  e_int := by
    intro j
    fin_cases j
    · exact ⟨310, by simp [shapeE]⟩
    · exact ⟨330, by simp [shapeE]⟩
  u_half := by
    intro i
    fin_cases i
    · exact ⟨603, by simp [shapeU]; norm_num⟩
    · exact ⟨23, by simp [shapeU]; norm_num⟩
    · exact ⟨19, by simp [shapeU]; norm_num⟩
    · exact ⟨15, by simp [shapeU]; norm_num⟩
    · exact ⟨11, by simp [shapeU]; norm_num⟩
    · exact ⟨7, by simp [shapeU]; norm_num⟩
    · exact ⟨3, by simp [shapeU]; norm_num⟩
    · exact ⟨-260, by simp [shapeU]; norm_num⟩
  v_int := hc0.v_int
  b_int := by
    intro j
    fin_cases j
    · exact ⟨300, by simp [shapeB]⟩
    · exact ⟨320, by simp [shapeB]⟩

variable (X : Fields) (Word : Type) (tops : Finset X.Tau)

def shapeHC (τ : X.Tau) : HCParam R0 := if τ ∈ tops then shapeTop else hc0

def shapeWts : Wts X Word R0 where
  row := fun τ => RowPar.of (shapeHC X tops τ)
  hc := fun _ τ => shapeHC X tops τ
  tops := tops

end Inst

section Inst2

open Formalism.BasicNotions.Examples₂

variable (X : Fields) (Pr : Primes X) (tops : Finset X.Tau)

end Inst2

end Formalism.L2.Col
