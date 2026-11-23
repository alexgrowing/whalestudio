import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.SymExp

namespace ReciprocityTheory.ChartRestriction.G.AI

theorem symm_swap_nat {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (f : ℕ → V) (a b : ℕ)
    (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  have h := hI (Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩) (fun j => f j)
  refine h.symm.trans (congrArg I (funext fun j => ?_))
  show f ((Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩ j : Fin n) : ℕ) =
    f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)
  refine congrArg f ?_
  by_cases h1 : (j : ℕ) = a
  · rw [if_pos h1]
    have hj : j = ⟨a, ha⟩ := Fin.ext h1
    simp [hj]
  · by_cases h2 : (j : ℕ) = b
    · rw [if_neg h1, if_pos h2]
      have hj : j = ⟨b, hb⟩ := Fin.ext h2
      simp [hj]
    · have h1' : j ≠ ⟨a, ha⟩ := fun h => h1 (congrArg Fin.val h)
      have h2' : j ≠ ⟨b, hb⟩ := fun h => h2 (congrArg Fin.val h)
      rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne h1' h2']

def interp {VW : Type*} (k i : ℕ) (x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j = 0 then x₂ else if j < 1 + 2 * i then x₁ else if j < 1 + 2 * k then x₂ else a

def consWord {VW : Type*} (k i : ℕ) (x x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j < 2 then x else if j = 2 then x₂ else if j < 3 + 2 * i then x₁ else
    if j < 1 + 2 * k then x₂ else a

theorem cons_cons_word {VW : Type*} (D k i : ℕ) (hk : 1 ≤ k) (x x₁ x₂ a : VW) :
    (Fin.cons x (Fin.cons x (word D k i x₁ x₂ a)) : Fin (D + 2) → VW) =
      fun j : Fin (D + 2) => consWord k i x x₁ x₂ a j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [consWord]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [consWord]
    · simp only [Fin.cons_succ, consWord, word, Fin.val_succ]
      split_ifs <;> first | rfl | omega

theorem symm_consWord_left {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin (D + 2) => V) ℝ) (hI : IsSymmForm I) (k i : ℕ) (hi : i < k)
    (hD : 2 * k ≤ D + 1) (x₁ x₂ a : V) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  refine (symm_swap_nat I hI (consWord k i x₁ x₁ x₂ a) 0 2 (by omega) (by omega)).trans ?_
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega

theorem symm_consWord_right {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin (D + 2) => V) ℝ) (hI : IsSymmForm I) (k i : ℕ) (hi : i < k)
    (hD : 2 * k ≤ D + 1) (x₁ x₂ a : V) :
    I (fun j => consWord k i x₂ x₁ x₂ a j) = I (fun j => interp k i x₁ x₂ a j) := by
  refine (symm_swap_nat I hI (consWord k i x₂ x₁ x₂ a) 1 (2 * i + 1) (by omega)
    (by omega)).trans ?_
  refine (symm_swap_nat I hI (fun m => consWord k i x₂ x₁ x₂ a
    (if m = 1 then 2 * i + 1 else if m = 2 * i + 1 then 1 else m)) 2 (2 * i + 2) (by omega)
    (by omega)).trans ?_
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega

theorem aPrime_thm : APrimeStatement := by
  intro D S k hk hkD
  have hstep : ∀ i ∈ Finset.range k,
      S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) =
        S.IW (fun j => interp k (i + 1) (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) -
          S.IW (fun j => interp k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← S.diag, cons_cons_word D k i hk, cons_cons_word D k i hk,
      symm_consWord_left S.IW S.symmW k i hi hkD,
      symm_consWord_right S.IW S.symmW k i hi hkD]
  have hsum : ∑ i ∈ Finset.range k, S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) =
      S.IW (fun j => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) -
        S.IW (fun j => interp k 0 (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    rw [Finset.sum_congr rfl hstep]
    exact Finset.sum_range_sub
      (fun m => S.IW (fun j => interp k m (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j)) k
  have hzero : S.IW (fun j => interp k 0 (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) = 0 := by
    have h := S.comp_right_eq_zero_alt
      (fun j : Fin (D + 2) => if (j : ℕ) < 1 + 2 * k then S.ξ else S.A)
    refine Eq.trans ?_ h
    congr 1
    funext j
    simp only [interp]
    split_ifs <;> first | rfl | exact S.base | omega
  have hfun : (Fin.cons (S.p₂ S.ξ) (fun j => S.p₁ (mix (2 * k) S.ξ S.A j)) :
      Fin (D + 2) → S.VW) =
      fun j : Fin (D + 2) => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) (j : ℕ) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [interp]
    · rw [Fin.cons_succ, Fin.val_succ]
      show S.p₁ (if (j : ℕ) < 2 * k then S.ξ else S.A) =
        (if (j : ℕ) + 1 = 0 then S.p₂ S.ξ else if (j : ℕ) + 1 < 1 + 2 * k then S.p₁ S.ξ else
          if (j : ℕ) + 1 < 1 + 2 * k then S.p₂ S.ξ else S.p₁ S.A)
      have h0 : ¬((j : ℕ) + 1 = 0) := by omega
      by_cases h : (j : ℕ) < 2 * k
      · have h1 : (j : ℕ) + 1 < 1 + 2 * k := by omega
        rw [if_pos h, if_neg h0, if_pos h1]
      · have h1 : ¬((j : ℕ) + 1 < 1 + 2 * k) := by omega
        rw [if_neg h, if_neg h0, if_neg h1, if_neg h1]
  have htop : S.I (mix (2 * k) S.ξ S.A) =
      -S.IW (fun j => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    rw [← S.cons_comp_left, show -(S.p₂ S.ξ) = (-1 : ℝ) • S.p₂ S.ξ by simp,
      MultilinearMap.cons_smul, neg_one_smul, hfun]
  rw [hsum, hzero, htop, sub_zero]

end ReciprocityTheory.ChartRestriction.G.AI
