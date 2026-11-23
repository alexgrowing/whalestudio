import Formalism.LogVandermondeBounds.MultinomialPowerBound

namespace Formalism.LogVandermondeBounds.flipTwoThree

open Finset

lemma term_le_B0 {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) : nu i - lam i.succ ≤ B0 lam nu := by
  unfold B0
  exact Finset.single_le_sum (f := fun k => nu k - lam k.succ)
    (fun k _ => by have := (h.2 k).1; linarith) (Finset.mem_univ i)

lemma loss_bound_nonneg {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    0 ≤ B0 lam nu := by
  unfold B0
  exact Finset.sum_nonneg (fun k _ => by have := (h.2 k).1; linarith)

lemma len_nonneg {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) : 0 ≤ len lam i := by
  unfold len
  have := h.2 i
  linarith [this.1, this.2]

lemma mem_Iset_of {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu' : Fin n → ℤ} {b : ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = b) (i : Fin n) : nu' i ∈ Iset lam b i := by
  have hle := term_le_B0 h' i
  have hi := h'.2 i
  have h1 : nu' i - lam i.succ ≤ min (len lam i) b :=
    le_min (by unfold len; linarith [hi.2]) (by rw [← hb]; exact hle)
  simp only [Iset, Finset.mem_Icc]
  constructor
  · linarith [hi.1]
  · linarith

lemma Iset_disj {n : ℕ} {lam : Fin (n + 1) → ℤ} (ha : Antitone lam) (b : ℤ) (i j : Fin n)
    (hij : i ≠ j) :
    Disjoint ((Iset lam b i).image (fun y => y - (i : ℤ)))
      ((Iset lam b j).image (fun y => y - (j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_image, Iset, Finset.mem_Icc] at hx hx'
  obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ := hx
  obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := hx'
  have hmi : min (len lam i) b ≤ lam i.castSucc - lam i.succ := min_le_left _ _
  have hmj : min (len lam j) b ≤ lam j.castSucc - lam j.succ := min_le_left _ _
  rcases lt_or_gt_of_ne hij with h | h
  · have h2 : lam j.castSucc ≤ lam i.succ := ha (Fin.succ_le_castSucc_iff.mpr h)
    have h3 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    omega
  · have h2 : lam i.castSucc ≤ lam j.succ := ha (Fin.succ_le_castSucc_iff.mpr h)
    have h3 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    omega

lemma sep_self_ne_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    sep lam nu nu ≠ 0 := by
  unfold sep
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro y hy
  rw [Finset.mem_erase] at hy
  unfold ev
  rw [Finset.prod_ne_zero_iff]
  intro j _ h0
  by_cases hij : i = j
  · subst hij
    exact hy.1 (by linarith)
  · have hyj : y - (i : ℤ) = nu j - (j : ℤ) := by linarith
    have m1 : y - (i : ℤ) ∈ (Iset lam (B0 lam nu) i).image (fun y => y - (i : ℤ)) :=
      Finset.mem_image_of_mem _ hy.2
    have m2 : y - (i : ℤ) ∈ (Iset lam (B0 lam nu) j).image (fun y => y - (j : ℤ)) := by
      rw [hyj]
      exact Finset.mem_image_of_mem _ (mem_Iset_of h rfl j)
    exact Finset.disjoint_left.mp (Iset_disj h.1 _ i j hij) m1 m2

lemma card_erase_Iset {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) :
    ((Iset lam (B0 lam nu) i).erase (nu i)).card = (min (len lam i) (B0 lam nu)).toNat := by
  rw [Finset.card_erase_of_mem (mem_Iset_of h rfl i)]
  unfold Iset
  rw [Int.card_Icc]
  have h0 : 0 ≤ min (len lam i) (B0 lam nu) := le_min (len_nonneg h i) (loss_bound_nonneg h)
  omega

lemma factor_bound {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i j : Fin n) (y : ℤ) (hy : y ∈ Iset lam (B0 lam nu) i) :
    |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ lam 0 - lam (Fin.last n) + n + 1 := by
  simp only [Iset, Finset.mem_Icc] at hy
  have hmi : min (len lam i) (B0 lam nu) ≤ lam i.castSucc - lam i.succ := min_le_left _ _
  have a1 : lam (Fin.last n) ≤ lam j.succ := h.1 (Fin.le_last _)
  have a2 : lam j.castSucc ≤ lam 0 := h.1 (Fin.zero_le _)
  have a3 : lam (Fin.last n) ≤ lam i.succ := h.1 (Fin.le_last _)
  have a4 : lam i.castSucc ≤ lam 0 := h.1 (Fin.zero_le _)
  have hj := h.2 j
  have il : ((i : ℕ) : ℤ) < n := by exact_mod_cast i.isLt
  have jl : ((j : ℕ) : ℤ) < n := by exact_mod_cast j.isLt
  rw [abs_le]
  constructor <;> omega

lemma sep_self_abs {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    |sep lam nu nu| ≤ (lam 0 - lam (Fin.last n) + n + 1) ^
      (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) := by
  set W : ℤ := lam 0 - lam (Fin.last n) + n + 1 with hW
  have inner : ∀ i : Fin n, |∏ y ∈ (Iset lam (B0 lam nu) i).erase (nu i), ev nu (y - (i : ℤ))|
      ≤ W ^ (n * (min (len lam i) (B0 lam nu)).toNat) := by
    intro i
    rw [Finset.abs_prod, ← card_erase_Iset h i, pow_mul, ← Finset.prod_const (W ^ n)]
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
    intro y hy
    have hyI := (Finset.mem_erase.mp hy).2
    unfold ev
    rw [Finset.abs_prod]
    calc ∏ j, |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ ∏ _j : Fin n, W :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => factor_bound h i j y hyI)
      _ = W ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold sep
  rw [Finset.abs_prod, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => inner i)

lemma sep_other_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu nu' : Fin n → ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = B0 lam nu) (hne : nu' ≠ nu) :
    sep lam nu nu' = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  unfold sep
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (i := nu' i) (Finset.mem_erase.mpr ⟨hi, mem_Iset_of h' hb i⟩)
  unfold ev
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

theorem interlacing_separation : InterlacingSeparation := by
  intro n lam nu h
  exact ⟨fun nu' h' hb i => mem_Iset_of h' hb i,
    fun i j hij => Iset_disj h.1 _ i j hij,
    sep_self_ne_zero h,
    sep_self_abs h,
    fun nu' h' hb hne => sep_other_zero h' hb hne⟩

end Formalism.LogVandermondeBounds.flipTwoThree
