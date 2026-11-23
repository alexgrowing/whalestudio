import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom

open Finset

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.GelfandTsetlinBases Formalism.CountingSumsFrames
open Formalism.L2.G.Model (Intl SSZ intl_zero card_SSZ card_ssIdx weylQ)

theorem sum_le_succ {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b ≤ a.succ, F b) = F 0 + ∑ b : Fin k with b ≤ a, F b.succ := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  simp [Fin.succ_le_succ_iff]

theorem sum_lt_succ {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b < a.succ, F b) = F 0 + ∑ b : Fin k with b < a, F b.succ := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  simp [Fin.succ_lt_succ_iff, Fin.succ_pos]

theorem sum_le_zero {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b ≤ 0, F b) = F 0 := by
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

def TX (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Type :=
  {g : Fin (m + 1) → Fin (m + 1) → ℕ // (Intl g ∧ ∀ t, ∑ a, g a t = ν t) ∧
    (top = true → (vec = true → g 0 0 = ν 0) ∧ (vec = false → ∀ t, g 0 t = 0))}

def xsEquiv (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : ↥(Xs m top vec ν) ≃ TX m top vec ν :=
  Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (Equiv.curry (Fin (m + 1)) (Fin (m + 1)) ℕ)) (by
    intro e
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨fun l j hlj a => ?_, fun t => h2 t⟩, h3⟩
      have := h1 l j hlj a
      rw [zero_add] at this
      exact this
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨fun l j hlj a => ?_, fun t => h2 t⟩, h3⟩
      rw [zero_add]
      exact h1 l j hlj a)

def TN (m : ℕ) (κ : Fin m → ℕ) : Type :=
  {g : Fin m → Fin m → ℕ // Intl g ∧ ∀ t, ∑ a, g a t = κ t}

def tnEquiv (m : ℕ) (κ : Fin m → ℕ) : TN m κ ≃ SSZ m (fun t => (κ t : ℤ)) :=
  Equiv.subtypeEquivRight (by
    intro g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t => congrArg Nat.cast (h2 t)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t => Nat.cast_injective (R := ℤ) (h2 t)⟩)

theorem card_TN (m : ℕ) (κ : Fin m → ℕ) : Nat.card (TN m κ) = dGT m (fun t => (κ t : ℤ)) := by
  rw [Nat.card_congr (tnEquiv m κ), card_SSZ _ _ (fun t => Nat.cast_nonneg _)]

def dropE {m : ℕ} (g : Fin (m + 1) → Fin (m + 1) → ℕ) : Fin m → Fin m → ℕ := fun a t => g a.succ t.succ

def addE {m : ℕ} (n0 : ℕ) (g : Fin m → Fin m → ℕ) : Fin (m + 1) → Fin (m + 1) → ℕ :=
  fun a t => Fin.cases (Fin.cases n0 (fun _ => 0) t) (fun a' => Fin.cases 0 (fun t' => g a' t') t) a

theorem intertwining_zero_succ {m : ℕ} {g : Fin (m + 1) → Fin (m + 1) → ℕ} (hg : Intl g) (t : Fin m) : g 0 t.succ = 0 := intl_zero g hg _ t.succ rfl 0 (by simp [Fin.val_succ])

theorem dropE_intl {m : ℕ} {g : Fin (m + 1) → Fin (m + 1) → ℕ} (hg : Intl g) : Intl (dropE g) := by
  intro l j hlj a
  have h := hg l.succ j.succ (by simp [Fin.val_succ, hlj]) a.succ
  rw [sum_le_succ (fun b => g b j.succ), sum_lt_succ (fun b => g b l.succ), intertwining_zero_succ hg, intertwining_zero_succ hg] at h
  simpa [dropE] using h

theorem dropE_sum {m : ℕ} {g : Fin (m + 1) → Fin (m + 1) → ℕ} (hg : Intl g) (t : Fin m) :
    ∑ a, dropE g a t = ∑ a, g a t.succ := by
  rw [Fin.sum_univ_succ (fun a => g a t.succ), intertwining_zero_succ hg, zero_add]
  rfl

theorem addE_intl {m : ℕ} (n0 : ℕ) {g : Fin m → Fin m → ℕ} (hg : Intl g) (h0 : ∀ t, ∑ a, g a t ≤ n0) :
    Intl (addE n0 g) := by
  intro l j hlj a
  induction j using Fin.cases with
  | zero => simp at hlj
  | succ j' =>
    induction a using Fin.cases with
    | zero =>
      rw [sum_le_zero]
      simp [addE]
    | succ a' =>
      rw [sum_le_succ, sum_lt_succ]
      induction l using Fin.cases with
      | zero =>
        have h1 : ∑ b : Fin m with b ≤ a', g b j' ≤ n0 :=
          le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (h0 j')
        simpa [addE] using h1
      | succ l' =>
        have h1 := hg l' j' (by simp [Fin.val_succ] at hlj; omega) a'
        simpa [addE] using h1

theorem addE_sum_zero {m : ℕ} (n0 : ℕ) (g : Fin m → Fin m → ℕ) : ∑ a, addE n0 g a 0 = n0 := by
  simp [addE, Fin.sum_univ_succ]

theorem addE_sum_succ {m : ℕ} (n0 : ℕ) (g : Fin m → Fin m → ℕ) (t : Fin m) :
    ∑ a, addE n0 g a t.succ = ∑ a, g a t := by
  simp [addE, Fin.sum_univ_succ]

def equivE (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : ∀ t : Fin m, ν t.succ ≤ ν 0) :
    TX m true true ν ≃ TN m (fun t => ν t.succ) where
  toFun g := ⟨dropE g.1, dropE_intl g.2.1.1, fun t => by rw [dropE_sum g.2.1.1, g.2.1.2]⟩
  invFun g := ⟨addE (ν 0) g.1, ⟨addE_intl _ g.2.1 (fun t => by rw [g.2.2]; exact hν t), fun t => by
      refine Fin.cases ?_ (fun t' => ?_) t
      · exact addE_sum_zero _ _
      · rw [addE_sum_succ, g.2.2]⟩, fun _ => ⟨fun _ => rfl, fun h => by simp at h⟩⟩
  left_inv g := by
    apply Subtype.ext
    funext a t
    have h00 : g.1 0 0 = ν 0 := (g.2.2 rfl).1 rfl
    refine Fin.cases ?_ (fun a' => ?_) a
    · refine Fin.cases ?_ (fun t' => ?_) t
      · exact h00.symm
      · exact (intertwining_zero_succ g.2.1.1 t').symm
    · refine Fin.cases ?_ (fun t' => ?_) t
      · have h1 := g.2.1.2 0
        rw [Fin.sum_univ_succ, h00] at h1
        have h2 : g.1 a'.succ 0 ≤ ∑ i : Fin m, g.1 i.succ 0 :=
          Finset.single_le_sum (f := fun i : Fin m => g.1 i.succ 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a')
        show 0 = g.1 a'.succ 0
        omega
      · rfl
  right_inv g := by
    apply Subtype.ext
    funext a t
    rfl

def dropO {m : ℕ} (g : Fin (m + 1) → Fin (m + 1) → ℕ) : Fin m → Fin m → ℕ := fun a t => g a.succ t.castSucc

def addO {m : ℕ} (g : Fin m → Fin m → ℕ) : Fin (m + 1) → Fin (m + 1) → ℕ :=
  fun a t => Fin.cases 0 (fun a' => Fin.lastCases 0 (fun t' => g a' t') t) a

theorem addO_zero {m : ℕ} (g : Fin m → Fin m → ℕ) (t : Fin (m + 1)) : addO g 0 t = 0 := rfl

theorem addO_last {m : ℕ} (g : Fin m → Fin m → ℕ) (a : Fin (m + 1)) : addO g a (Fin.last m) = 0 := by
  induction a using Fin.cases <;> simp [addO]

theorem addO_cc {m : ℕ} (g : Fin m → Fin m → ℕ) (a t : Fin m) : addO g a.succ t.castSucc = g a t := by
  simp [addO]

theorem dropO_intl {m : ℕ} {g : Fin (m + 1) → Fin (m + 1) → ℕ} (hg : Intl g) (h0 : ∀ t, g 0 t = 0) :
    Intl (dropO g) := by
  intro l j hlj a
  have h := hg l.castSucc j.castSucc (by simpa using hlj) a.succ
  rw [sum_le_succ (fun b => g b j.castSucc), sum_lt_succ (fun b => g b l.castSucc), h0, h0] at h
  simpa [dropO] using h

theorem dropO_sum {m : ℕ} {g : Fin (m + 1) → Fin (m + 1) → ℕ} (h0 : ∀ t, g 0 t = 0) (t : Fin m) :
    ∑ a, dropO g a t = ∑ a, g a t.castSucc := by
  rw [Fin.sum_univ_succ (fun a => g a t.castSucc), h0, zero_add]
  rfl

theorem addO_intl {m : ℕ} {g : Fin m → Fin m → ℕ} (hg : Intl g) : Intl (addO g) := by
  intro l j hlj a
  induction a using Fin.cases with
  | zero =>
    rw [sum_le_zero]
    simp [addO]
  | succ a' =>
    rw [sum_le_succ, sum_lt_succ]
    induction j using Fin.lastCases with
    | last => simp [addO]
    | cast j' =>
      have hl : l.val < m := by
        have := j'.isLt
        simp at hlj
        omega
      obtain ⟨l', rfl⟩ : ∃ l' : Fin m, l = l'.castSucc := ⟨⟨l.val, hl⟩, Fin.ext rfl⟩
      have h1 := hg l' j' (by simpa using hlj) a'
      simpa [addO] using h1

theorem addO_sum {m : ℕ} (g : Fin m → Fin m → ℕ) (t : Fin m) : ∑ a, addO g a t.castSucc = ∑ a, g a t := by
  simp [addO, Fin.sum_univ_succ]

def equivO (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : ν (Fin.last m) = 0) :
    TX m true false ν ≃ TN m (fun t => ν t.castSucc) where
  toFun g := ⟨dropO g.1, dropO_intl g.2.1.1 ((g.2.2 rfl).2 rfl), fun t => by
    rw [dropO_sum ((g.2.2 rfl).2 rfl), g.2.1.2]⟩
  invFun g := ⟨addO g.1, ⟨addO_intl g.2.1, fun t => by
      refine Fin.lastCases ?_ (fun t' => ?_) t
      · rw [hν]
        exact Finset.sum_eq_zero fun b _ => addO_last g.1 b
      · rw [addO_sum, g.2.2]⟩, fun _ => ⟨fun h => by simp at h, fun _ t => addO_zero g.1 t⟩⟩
  left_inv g := by
    apply Subtype.ext
    funext a t
    have h0 : ∀ t, g.1 0 t = 0 := (g.2.2 rfl).2 rfl
    refine Fin.cases ?_ (fun a' => ?_) a
    · exact (h0 t).symm
    · refine Fin.lastCases ?_ (fun t' => ?_) t
      · have h1 := g.2.1.2 (Fin.last m)
        rw [hν] at h1
        have h2 : g.1 a'.succ (Fin.last m) ≤ ∑ i, g.1 i (Fin.last m) :=
          Finset.single_le_sum (f := fun i => g.1 i (Fin.last m)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        show addO (dropO g.1) a'.succ (Fin.last m) = _
        rw [addO_last]
        omega
      · show addO (dropO g.1) a'.succ t'.castSucc = _
        rw [addO_cc]
        rfl
  right_inv g := by
    apply Subtype.ext
    funext a t
    show addO g.1 a.succ t.castSucc = _
    rw [addO_cc]

theorem dGT_weylDim (n : ℕ) (μ : Fin n → ℤ) (hμ : Antitone μ) : ((dGT n μ : ℕ) : ℚ) = weylDim n μ := by
  rw [weylQ n μ hμ]
  simp only [Formalism.CountingSumsFrames.weylDim, Int.cast_sub]

theorem nuOf_cast {m : ℕ} (lam : Fin (m + 1) → ℤ) (h : Antitone lam) (t : Fin (m + 1)) :
    ((nuOf lam t : ℕ) : ℤ) = lam t + (-lam (Fin.last m)) := by
  have h1 : lam (Fin.last m) ≤ lam t := h (Fin.le_last t)
  simp only [nuOf]
  rw [Int.toNat_of_nonneg (by linarith)]
  ring

theorem Xs_finite (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : (Xs m top vec ν).Finite := by
  have hb : ∀ g : TX m top vec ν, ∀ a t, g.1 a t < ν t + 1 := fun g a t => by
    have h1 : g.1 a t ≤ ∑ b, g.1 b t :=
      Finset.single_le_sum (f := fun b => g.1 b t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    rw [g.2.1.2 t] at h1
    omega
  have : Finite (TX m top vec ν) :=
    Finite.of_injective (fun g : TX m top vec ν => fun a t => (⟨g.1 a t, hb g a t⟩ : Fin (ν t + 1)))
      (fun g g' h => Subtype.ext (funext fun a => funext fun t => by
        have h2 := congrFun (congrFun h a) t
        simpa using h2))
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (xsEquiv m top vec ν).symm)

private lemma weylDim_add_const' (n : ℕ) (μ : Fin n → ℤ) (c : ℤ) :
    Formalism.CountingSumsFrames.weylDim n (fun t => μ t + c) = Formalism.CountingSumsFrames.weylDim n μ := by
  unfold Formalism.CountingSumsFrames.weylDim
  simp only [add_sub_add_right_eq_sub]

theorem cntSpec : CntSpec := by
  intro m lam hlam vec
  have e1 : TX m false vec (nuOf lam) ≃ TN (m + 1) (nuOf lam) :=
    Equiv.subtypeEquivRight (fun g => by simp)
  rw [Nat.card_congr ((xsEquiv m false vec (nuOf lam)).trans e1), card_TN]
  have hanti : Antitone (fun t => ((nuOf lam t : ℕ) : ℤ)) := by
    intro a b hab
    simp only [nuOf_cast lam hlam]
    linarith [hlam hab]
  rw [dGT_weylDim _ _ hanti]
  simp only [nuOf_cast lam hlam]
  exact weylDim_add_const' (m + 1) lam _

private lemma weylDim_const_sub_rev (m : ℕ) (μ : Fin m → ℤ) (c : ℤ) :
    Formalism.CountingSumsFrames.weylDim m (fun t => c - μ t.rev) = Formalism.CountingSumsFrames.weylDim m μ := by
  unfold Formalism.CountingSumsFrames.weylDim
  rw [Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun j => ?_)
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply]
  have hr : ∀ x : Fin m, ((x.rev : ℕ) : ℚ) = (m : ℚ) - 1 - ((x : ℕ) : ℚ) := by
    intro x
    have := x.isLt
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hr i, hr j]
  by_cases h : i < j
  · have h' : j.rev < i.rev := Fin.rev_lt_rev.mpr h
    rw [if_pos h, if_pos h']
    push_cast
    congr 1 <;> ring
  · have h' : ¬ j.rev < i.rev := fun h2 => h (Fin.rev_lt_rev.mp h2)
    rw [if_neg h, if_neg h']

theorem cntTop : CntTop := by
  intro m _ lo hlo _ vec
  cases vec with
  | true =>
    rw [if_pos rfl]
    have hν : ∀ t : Fin m, nuOf lo t.succ ≤ nuOf lo 0 := fun t => by
      have h1 := nuOf_cast lo hlo t.succ
      have h2 := nuOf_cast lo hlo 0
      have h3 := hlo (Fin.zero_le t.succ)
      omega
    rw [Nat.card_congr ((xsEquiv m true true (nuOf lo)).trans (equivE m (nuOf lo) hν)), card_TN]
    have hanti : Antitone (fun t : Fin m => ((nuOf lo t.succ : ℕ) : ℤ)) := by
      intro a b hab
      simp only [nuOf_cast lo hlo]
      linarith [hlo (Fin.succ_le_succ_iff.mpr hab)]
    rw [dGT_weylDim _ _ hanti]
    simp only [nuOf_cast lo hlo]
    exact weylDim_add_const' m (fun i => lo i.succ) _
  | false =>
    rw [if_neg Bool.false_ne_true]
    have hL : Antitone (fun i : Fin (m + 1) => -lo i.rev) := by
      intro a b hab
      have := hlo (Fin.rev_le_rev.mpr hab)
      simp only
      linarith
    have hν : nuOf (fun i : Fin (m + 1) => -lo i.rev) (Fin.last m) = 0 := by
      simp [nuOf]
    rw [Nat.card_congr ((xsEquiv m true false _).trans (equivO m _ hν)), card_TN]
    have hf : (fun t : Fin m => ((nuOf (fun i : Fin (m + 1) => -lo i.rev) t.castSucc : ℕ) : ℤ)) =
        fun t => lo 0 - lo t.rev.succ := by
      funext t
      rw [nuOf_cast _ hL]
      simp only [Fin.rev_castSucc, Fin.rev_last]
      ring
    have hanti : Antitone (fun t : Fin m => lo 0 - lo t.rev.succ) := by
      intro a b hab
      have := hlo (Fin.succ_le_succ_iff.mpr (Fin.rev_le_rev.mpr hab))
      simp only
      linarith
    rw [hf, dGT_weylDim _ _ hanti]
    exact weylDim_const_sub_rev m (fun i => lo i.succ) (lo 0)

open Formalism.MainNotions.Pf14 (restW dT flW flatDeg vecE remainingWeightVectorCount) in

theorem card_all {n' m : ℕ} (hm : 2 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hdom : IsDominant lam0) :
    ((Nat.card (∀ s : Fin n', ↥(Xs m (decide (s ∈ TT)) (vecE n' s) (nuOf (lamAt (restW TT lam0) s)))) : ℕ) : ℚ) =
      remainingWeightVectorCount TT lam0 := by
  have hR0 : ∀ s, s ∉ TT → restW TT lam0 s = lam0 s := by
    intro s hs
    funext i
    simp [restW, flW, dT, hs]
  have hR1 : ∀ s, s ∈ TT → ∀ i : Fin (m + 1), i ≠ 0 → restW TT lam0 s i = lam0 s i := by
    intro s hs i hi
    simp [restW, flW, Pi.single_apply, hi]
  have hR2 : ∀ s, s ∈ TT → restW TT lam0 s 0 = lam0 s 1 := by
    intro s hs
    have h01 : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le 1)
    simp [restW, flW, dT, hs, flatDeg, Int.toNat_of_nonneg (sub_nonneg.mpr h01)]
  have h1v : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    first
    | exact Nat.mod_eq_of_lt (by omega)
    | (simp; omega)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := fun h => by
    have := congrArg Fin.val h
    rw [h1v] at this
    simp at this
  have hAnti : ∀ s, s ∈ TT → Antitone (restW TT lam0 s) := by
    intro s hs a b hab
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb
        exact le_rfl
      · have hb1 : (1 : Fin (m + 1)) ≤ b := by
          rw [Fin.le_iff_val_le_val, h1v]
          have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
          omega
        rw [hR1 s hs b hb, hR2 s hs]
        exact hdom s hb1
    · have hb : b ≠ 0 := by
        rintro rfl
        exact ha (Fin.le_zero_iff.mp hab)
      rw [hR1 s hs a ha, hR1 s hs b hb]
      exact hdom s hab
  have hR01 : ∀ s, s ∈ TT → restW TT lam0 s 0 = restW TT lam0 s 1 := by
    intro s hs
    rw [hR2 s hs, hR1 s hs 1 h10]
  rw [Nat.card_pi]
  push_cast
  rw [← Finset.prod_mul_prod_compl TT]
  unfold remainingWeightVectorCount
  congr 1
  · refine Finset.prod_congr rfl fun s hs => ?_
    have hl : lamAt (restW TT lam0) s =
        if vecE n' s = true then restW TT lam0 s else fun i => -restW TT lam0 s i.rev := by
      simp [lamAt, vecE]
    rw [show decide (s ∈ TT) = true from decide_eq_true hs, hl,
      cntTop m hm _ (hAnti s hs) (hR01 s hs)]
    congr 1
    funext i
    exact hR1 s hs i.succ (Fin.succ_ne_zero i)
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [Finset.mem_compl] at hs
    rw [show decide (s ∈ TT) = false from decide_eq_false hs]
    have hA : Antitone (lamAt (restW TT lam0) s) := by
      unfold lamAt
      rw [hR0 s hs]
      split_ifs
      · exact hdom s
      · intro a b hab
        have := hdom s (Fin.rev_le_rev.mpr hab)
        simp only
        linarith
    rw [cntSpec m _ hA]
    unfold lamAt
    rw [hR0 s hs]
    split_ifs
    · rfl
    · have := weylDim_const_sub_rev (m + 1) (lam0 s) 0
      simpa using this

end Formalism.MainNotions.TestSideCounting
