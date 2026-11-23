import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame.SignWord

variable {n : ℕ}

def sg (b : Bool) : ℤ := cond b 1 (-1)

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

theorem step_sign (a b c e : Bool) (k : ℕ) (h : Xor' (a = b) (c = e)) :
    sg c * sg a * (-1 : ℤ) ^ k = sg e * sg b * (-1 : ℤ) ^ (k + 1) := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all [Xor', sg, pow_succ]

theorem sign_left (b : Bool) (k : ℕ) (h : sg b * sg true * (-1 : ℤ) ^ k = 1) :
    b = true ↔ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sign_right (b : Bool) (k : ℕ) (h : sg b * sg false * (-1 : ℤ) ^ k = 1) :
    b = true ↔ ¬ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sum_neg_one_pow (n : ℕ) : ∑ p ∈ range (2 * n + 1), (-1 : ℤ) ^ p = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h : (-1 : ℤ) ^ (2 * k + 1) = -1 := (odd_two_mul_add_one k).neg_one_pow
    have h' : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by rw [pow_succ, h]; norm_num
    rw [h, h']; norm_num

theorem above_lt_of_lt (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) {r : ℝ}
    (x : Fin (n + 1) ⊕ Fin n) (h : r < Sum.elim d d' x) :
    above d d' (Sum.elim d d' x) < above d d' r := by
  unfold above
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact h.trans hz
  · simpa using h
  · simp

theorem above_lt_card (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (x : Fin (n + 1) ⊕ Fin n) :
    above d d' (Sum.elim d d' x) < 2 * n + 1 := by
  have h : above d d' (Sum.elim d d' x) < (univ : Finset (Fin (n + 1) ⊕ Fin n)).card := by
    unfold above
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.2 ⟨x, mem_univ _, by simp⟩
  have h2 : (univ : Finset (Fin (n + 1) ⊕ Fin n)).card = 2 * n + 1 := by
    simp [Finset.card_univ, Fintype.card_sum]; ring
  omega

theorem above_injective (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    Function.Injective fun x => above d d' (Sum.elim d d' x) := by
  intro x y hxy
  simp only at hxy
  rcases lt_trichotomy (Sum.elim d d' x) (Sum.elim d d' y) with h | h | h
  · have := above_lt_of_lt d d' y h
    omega
  · exact hv h
  · have := above_lt_of_lt d d' x h
    omega

theorem above_image (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    (univ : Finset (Fin (n + 1) ⊕ Fin n)).image (fun x => above d d' (Sum.elim d d' x)) =
      range (2 * n + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.1 hp
    exact mem_range.2 (above_lt_card d d' x)
  · rw [Finset.card_image_of_injective _ (above_injective d d' hv)]
    simp [Finset.card_univ, Fintype.card_sum]
    omega

theorem sum_above (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    ∑ x : Fin (n + 1) ⊕ Fin n, (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = 1 := by
  have h := sum_neg_one_pow n
  rw [← above_image d d' hv,
    Finset.sum_image (fun x _ y _ h => above_injective d d' hv h)] at h
  exact h

theorem sum_signs (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e) :
    ∑ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft = 1 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i, sg (ε i) = ∑ a, sg (ε' a) + 1 := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    have h0 : sg (ε (e (Sum.inr ()))) = 1 := by
      have : ε (e (Sum.inr ())) = true := hf.1
      simp [this, sg]
    simp [hf.2, h0]
  have hl : sg true = 1 := rfl
  have hr : sg false = -1 := rfl
  simp [hl, hr, h1]

theorem step_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') (x y : Fin (n + 1) ⊕ Fin n)
    (hxy : above d d' (Sum.elim d d' y) = above d d' (Sum.elim d d' x) + 1) :
    sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
      sg (Sum.elim ε ε' y) * sg y.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' y) := by
  have hlt : Sum.elim d d' y < Sum.elim d d' x := by
    rcases lt_trichotomy (Sum.elim d d' y) (Sum.elim d d' x) with h | h | h
    · exact h
    · rw [h] at hxy; omega
    · have := above_lt_of_lt d d' y h
      omega
  have hno : ∀ z, ¬ (Sum.elim d d' y < Sum.elim d d' z ∧ Sum.elim d d' z < Sum.elim d d' x) := by
    rintro z ⟨h1, h2⟩
    have a1 := above_lt_of_lt d d' z h1
    have a2 := above_lt_of_lt d d' x h2
    omega
  have := hw x y hlt hno
  rw [hxy]
  exact step_sign _ _ _ _ _ (by
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩)

theorem const_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    ∃ T : ℤ, ∀ x : Fin (n + 1) ⊕ Fin n,
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = T := by
  have him := above_image d d' hv
  have hsurj : ∀ p < 2 * n + 1, ∃ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p := by
    intro p hp
    have : p ∈ (univ : Finset (Fin (n + 1) ⊕ Fin n)).image
        (fun x => above d d' (Sum.elim d d' x)) := by
      rw [him]; exact mem_range.2 hp
    obtain ⟨x, -, hx⟩ := mem_image.1 this
    exact ⟨x, hx⟩
  obtain ⟨x0, hx0⟩ := hsurj 0 (by omega)
  refine ⟨sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0), ?_⟩
  have key : ∀ p : ℕ, ∀ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p →
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
        sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0) := by
    intro p
    induction p with
    | zero =>
      intro x hx
      have : x = x0 := above_injective d d' hv (by simp only [hx, hx0])
      rw [this]
    | succ k ih =>
      intro x hx
      have hk : k < 2 * n + 1 := by
        have := above_lt_card d d' x
        omega
      obtain ⟨y, hy⟩ := hsurj k hk
      rw [← ih y hy]
      exact (step_letters ε d ε' d' hv hw y x (by rw [hx, hy])).symm
  exact fun x => key _ x rfl

theorem heSign (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e)
    (hv : Function.Injective (Sum.elim d d')) (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧
      ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  obtain ⟨T, hT⟩ := const_letters ε d ε' d' hv hw
  have hsum : T = 1 := by
    have h1 : ∀ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft =
        T * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) := by
      intro x
      rw [← hT x]
      have hp : ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) *
          ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) = 1 := by
        rw [← mul_pow]; simp
      rw [mul_assoc, hp, mul_one]
    have h2 := sum_signs ε ε' e hf
    simp_rw [h1] at h2
    rw [← Finset.mul_sum, sum_above d d' hv] at h2
    simpa using h2
  subst hsum
  refine ⟨fun i => sign_left _ _ (by simpa using hT (Sum.inl i)),
    fun j => sign_right _ _ (by simpa using hT (Sum.inr j))⟩

end GlobalTheory.CompanionTheory.RgHeFrame.SignWord
