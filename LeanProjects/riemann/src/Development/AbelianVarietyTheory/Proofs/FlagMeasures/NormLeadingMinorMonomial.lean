import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem partialProd_inv_le (t : ℕ → ℝ) (ht : ∀ a, 0 < t a) (j : ℕ) (De : ℝ)
    (h : ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ De ∨ (0 < b ∧ b < j ∧ t (b - 1) = t b)) :
    ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ De := by
  have hP : ∀ b, 0 < ∏ a ∈ Finset.range b, t a := fun b => Finset.prod_pos fun a _ => ht a
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (j + 1))
    (fun b => (∏ a ∈ Finset.range b, t a)⁻¹) ⟨0, by simp⟩
  have hle : ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ (∏ a ∈ Finset.range m, t a)⁻¹ :=
    fun b hb => hmax b (Finset.mem_range.2 (Nat.lt_succ_of_le hb))

  have key : ∀ b, b ≤ j → (∏ a ∈ Finset.range b, t a)⁻¹ = (∏ a ∈ Finset.range m, t a)⁻¹ →
      (∏ a ∈ Finset.range m, t a)⁻¹ ≤ De := by
    intro b
    induction b with
    | zero =>
      intro hb h0
      rcases h 0 hb with h1 | ⟨h1, -, -⟩
      · rw [← h0]; exact h1
      · exact absurd h1 (lt_irrefl 0)
    | succ n ih =>
      intro hn heq
      rcases h (n + 1) hn with h1 | ⟨-, hlt, hteq⟩
      · rw [← heq]; exact h1
      · rw [Nat.add_sub_cancel] at hteq
        apply ih (Nat.le_of_succ_le hn)
        have hx := hP n
        have hc := ht n
        have h0 := hle n (Nat.le_of_succ_le hn)
        have h2 := hle (n + 1 + 1) (by omega)
        rw [← heq] at h0 h2 ⊢
        rw [Finset.prod_range_succ] at h0 ⊢
        rw [Finset.prod_range_succ, Finset.prod_range_succ, ← hteq] at h2
        rw [inv_le_inv₀ hx (mul_pos hx hc)] at h0
        rw [inv_le_inv₀ (mul_pos (mul_pos hx hc) hc) (mul_pos hx hc)] at h2
        have c1 : t n ≤ 1 := by nlinarith
        have c2 : 1 ≤ t n := by nlinarith [mul_pos hx hc]
        rw [le_antisymm c1 c2, mul_one]
  intro b hb
  exact (hle b hb).trans (key m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) rfl)

theorem norm_leading_minor_monomial {j l : ℕ} (hl : l ≤ j) (Z : Matrix (Fin j) (Fin j) ℂ) (w : Equiv.Perm (Fin j))
    (hw : ∀ a b, Z a b ≠ 0 ↔ b = w a) (hc : ∀ a : Fin j, a.val < l → (w a).val < l) :
    ‖(Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖ = ∏ a : Fin l, ‖Z (Fin.castLE hl a) (w (Fin.castLE hl a))‖ := by
  set M := Z.submatrix (Fin.castLE hl) (Fin.castLE hl) with hM

  let f : Fin l → Fin l := fun a => ⟨(w (Fin.castLE hl a)).val, hc _ a.2⟩
  have hcf : ∀ a, Fin.castLE hl (f a) = w (Fin.castLE hl a) := fun a => Fin.ext rfl
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg (Fin.castLE hl) hab
    rw [hcf, hcf] at h1
    exact Fin.castLE_injective hl (w.injective h1)
  let w' : Equiv.Perm (Fin l) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hw' : ∀ a, w' a = f a := fun a => rfl
  have hMne : ∀ a b, M a b ≠ 0 ↔ b = w' a := by
    intro a b
    rw [hM, Matrix.submatrix_apply, hw, hw', ← hcf]
    exact (Fin.castLE_injective hl).eq_iff

  rw [Matrix.det_apply', Finset.sum_eq_single w'.symm]
  · have hs : ‖((Equiv.Perm.sign w'.symm : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign w'.symm) with hsg | hsg <;> simp [hsg]
    rw [norm_mul, hs, one_mul, norm_prod]
    refine Fintype.prod_equiv w'.symm _ _ fun i => ?_
    have hi : Fin.castLE hl i = w (Fin.castLE hl (w'.symm i)) := by
      rw [← hcf, ← hw', Equiv.apply_symm_apply]
    show ‖Z (Fin.castLE hl (w'.symm i)) (Fin.castLE hl i)‖ = _
    rw [hi]
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, w' (σ i) ≠ i := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext fun i => w'.eq_symm_apply.2 (hne i))
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_contra hz
    exact hi ((hMne (σ i) i).1 hz).symm
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem blockAnti_perm_partialProd : ∀ (j : ℕ) (β : Fin j → ℕ) (Z : Matrix (Fin j) (Fin j) ℂ) (De : ℝ), BlockAnti β Z → 1 ≤ De → (∀ (l : ℕ) (hl : l ≤ j), (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 → ‖(Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖⁻¹ ≤ De) → ∃ (w : Equiv.Perm (Fin j)), (∀ a b, Z a b ≠ 0 ↔ b = w a) ∧ (∀ a, β (w a) = β a) ∧ ∀ b : ℕ, (∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b), ‖Z a (w a)‖)⁻¹ ≤ De := by
  intro j β Z De hZ _ hminor
  unfold BlockAnti at hZ
  obtain ⟨hmono, hdet, hblk, hanti⟩ := hZ

  have hrow : ∀ a, ∃ b, Z a b ≠ 0 := by
    intro a
    by_contra hne
    push_neg at hne
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero a hne)
  choose f hf using hrow
  have huniq : ∀ a b, Z a b ≠ 0 → b = f a := fun a b hab =>
    (hanti a b a (f a) hab (hf a) rfl).2.1 rfl

  have hinj : Function.Injective f := by
    intro a a' h
    have h1 := hf a
    have h2 := hf a'
    rw [← h] at h2
    have hb : β a = β a' := (hblk a (f a) h1).trans (hblk a' (f a) h2).symm
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exact absurd ((hanti a (f a) a' (f a) h1 h2 hb).2.2 hlt) (lt_irrefl _)
    · exact heq
    · exact absurd ((hanti a' (f a) a (f a) h2 h1 hb.symm).2.2 hgt) (lt_irrefl _)
  let w : Equiv.Perm (Fin j) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hw : ∀ a b, Z a b ≠ 0 ↔ b = w a := fun a b =>
    ⟨huniq a b, fun h => by rw [h]; exact hf a⟩
  have hβ : ∀ a, β (w a) = β a := fun a => (hblk a (w a) (hf a)).symm
  refine ⟨w, hw, hβ, ?_⟩

  let t : ℕ → ℝ := fun n => if h : n < j then ‖Z ⟨n, h⟩ (w ⟨n, h⟩)‖ else 1
  have ht : ∀ n, 0 < t n := by
    intro n
    simp only [t]
    split_ifs with h
    · exact norm_pos_iff.2 (hf _)
    · exact one_pos
  have htfin : ∀ a : Fin j, t a.val = ‖Z a (w a)‖ := by
    intro a
    simp [t]
  have hconv : ∀ b, ∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b), ‖Z a (w a)‖ =
      ∏ n ∈ Finset.range (min b j), t n := by
    intro b
    rw [Finset.prod_filter]
    simp_rw [← htfin]
    refine (Fin.prod_univ_eq_prod_range (fun n => if n < b then t n else 1) j).trans ?_
    rw [← Finset.prod_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    exact and_comm

  have hh : ∀ l ≤ j, (∏ n ∈ Finset.range l, t n)⁻¹ ≤ De ∨ (0 < l ∧ l < j ∧ t (l - 1) = t l) := by
    intro l hl
    by_cases hbd : ∀ a : Fin j, a.val < l → (w a).val < l
    · left
      have hnorm := norm_leading_minor_monomial hl Z w hw hbd
      have hprod : ∏ a : Fin l, ‖Z (Fin.castLE hl a) (w (Fin.castLE hl a))‖ = ∏ n ∈ Finset.range l, t n := by
        rw [← Fin.prod_univ_eq_prod_range]
        exact Finset.prod_congr rfl fun a _ => (htfin (Fin.castLE hl a)).symm
      have hpos : 0 < ∏ n ∈ Finset.range l, t n := Finset.prod_pos fun n _ => ht n
      have hne : (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
        intro h0
        rw [h0, norm_zero, hprod] at hnorm
        linarith
      have hb := hminor l hl hne
      rw [hnorm, hprod] at hb
      exact hb
    · right
      push_neg at hbd
      obtain ⟨a, hal, hwa⟩ := hbd
      have hlj : l < j := lt_of_le_of_lt hwa (w a).2
      have hl0 : 0 < l := lt_of_le_of_lt (Nat.zero_le _) hal
      refine ⟨hl0, hlj, ?_⟩
      let p : Fin j := ⟨l - 1, by omega⟩
      let q : Fin j := ⟨l, hlj⟩
      have hβeq : β p = β q := by
        have h1 : β a ≤ β p := hmono (Fin.le_def.2 (show a.val ≤ l - 1 by omega))
        have h2 : β p ≤ β q := hmono (Fin.le_def.2 (show l - 1 ≤ l by omega))
        have h3 : β q ≤ β (w a) := hmono (Fin.le_def.2 hwa)
        rw [hβ a] at h3
        omega
      have e1 : t (l - 1) = ‖Z p (w p)‖ := htfin p
      have e2 : t l = ‖Z q (w q)‖ := htfin q
      rw [e1, e2]
      exact (hanti p (w p) q (w q) (hf p) (hf q) hβeq).1
  intro b
  rw [hconv]
  exact partialProd_inv_le t ht j De hh (min b j) (min_le_right _ _)

end GlobalTheory.Amp
