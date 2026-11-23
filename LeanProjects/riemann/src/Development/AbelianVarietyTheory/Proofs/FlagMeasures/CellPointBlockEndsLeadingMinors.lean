import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.FormalDegreeBessel.FinalG
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PtMinor

noncomputable def minor (bs : List (ℂ × ℕ)) (m : ℕ) : ℂ := (Matrix.of fun a b : Fin m => ptEntry bs a b).det

def ends (c : ℕ) (bs : List (ℂ × ℕ)) : List ℕ := ((bs.map Prod.snd).scanl (· + ·) c).tail

theorem ends_nil (c : ℕ) : ends c [] = [] := by simp [ends]

theorem ends_cons (c : ℕ) (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) :
    ends c ((t, s) :: bs) = (c + s) :: ends (c + s) bs := by
  cases bs <;> simp [ends]

theorem det_anti (t : ℂ) (ht : t ≠ 0) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det ≠ 0 := by
  have : (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) =
      (Matrix.diagonal fun _ : Fin s => t).submatrix (Fin.revPerm : Equiv.Perm (Fin s)) id := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.revPerm_apply, id, Fin.ext_iff,
      Fin.val_rev]
    have := a.2
    exact if_congr (by omega) rfl rfl
  rw [this, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h | h <;> simp [h, ht]

theorem minor_cons (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) :
    minor ((t, s) :: bs) (s + m) =
      (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det * minor bs m := by
  unfold minor
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin s) (Fin m) ℂ),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [ptEntry]

theorem minor_lt (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) (h1 : 1 ≤ m) (h2 : m < s) :
    minor ((t, s) :: bs) m = 0 := by
  unfold minor
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h1⟩ fun j => ?_
  have := j.2
  simp only [Matrix.of_apply, ptEntry]
  split_ifs <;> first | rfl | omega

theorem ends_bd (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c : ℕ) :
    (∀ x ∈ ends c bs, c < x ∧ x ≤ c + (bs.map Prod.snd).sum) ∧ (ends c bs).Nodup ∧
      (bs ≠ [] → c + (bs.map Prod.snd).sum ∈ ends c bs) := by
  induction bs generalizing c with
  | nil => simp [ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    obtain ⟨i1, i2, i3⟩ := ih (fun b hb => h b (by simp [hb])) (c + s)
    rw [ends_cons]
    simp only [List.map_cons, List.sum_cons, List.mem_cons, List.nodup_cons]
    refine ⟨?_, ⟨fun hm => ?_, i2⟩, fun _ => ?_⟩
    · rintro x (rfl | hx)
      · omega
      · have := i1 x hx
        omega
    · have := i1 _ hm
      omega
    · by_cases hb : bs = []
      · subst hb; simp
      · right
        rw [← add_assoc]
        exact i3 hb

theorem minor_ne_iff (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c l : ℕ) (hl : 1 ≤ l) :
    minor bs l ≠ 0 ↔ c + l ∈ ends c bs := by
  induction bs generalizing c l with
  | nil =>
    have : minor [] l = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hl⟩ fun j => by simp [ptEntry]
    simp [this, ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have h' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb => h b (by simp [hb])
    have hb := (ends_bd bs h' (c + s)).1
    rw [ends_cons, List.mem_cons]
    rcases lt_or_ge l s with hls | hls
    · rw [minor_lt t s bs l hl hls]
      refine ⟨fun h0 => absurd rfl h0, ?_⟩
      rintro (h1 | h1)
      · omega
      · have := hb _ h1
        omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hls
      rw [minor_cons, mul_ne_zero_iff, and_iff_right (det_anti t ht s)]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [minor]
      · rw [ih h' (c + s) m hm, add_assoc]
        refine ⟨Or.inr, ?_⟩
        rintro (h1 | h1)
        · omega
        · exact h1

theorem one_le_max_inv (x : ℝ) (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hx).2 h)

theorem list_prod (L : List ℕ) (f : ℕ → ℝ) (hf : ∀ l ∈ L, 1 ≤ f l) (a a' : ℝ) (ha : 0 ≤ a) (ha' : a ≤ a') :
    1 ≤ (L.map fun l => f l ^ a).prod ∧ (L.map fun l => f l ^ a).prod ≤ (L.map fun l => f l ^ a').prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨i1, i2⟩ := ih fun l hl => hf l (by simp [hl])
    have hx : 1 ≤ f x := hf x (by simp)
    have h1 := Real.one_le_rpow hx ha
    have h2 := Real.rpow_le_rpow_of_exponent_le hx ha'
    simp only [List.map_cons, List.prod_cons]
    exact ⟨one_le_mul_of_one_le_of_one_le h1 i1, mul_le_mul h2 i2 (by linarith) (by linarith)⟩

theorem one_le_foldr (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons x L ih => exact le_max_of_le_right ih

theorem blockEnds_minors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  intro D z z' γ p hz hz' hT hT' hRel
  obtain ⟨hU, ⟨L, U, hL, hU', hZ⟩, hG⟩ := hRel
  have hp := p.2.1
  have hsum := p.2.2
  obtain ⟨e1, e2, e3⟩ := ends_bd p.1 hp 0
  rw [zero_add, hsum] at e1 e3
  have key : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (DminN z z' γ l) = Complex.normSq (minor p.1 l) := by
    intro l hl
    have h1 := Formalism.MainNotions.S.Bridge.normSq_leadMinor_ZhatO D.R.k D.R.rS z z' γ l hl
    rw [hZ, Formalism.MainNotions.S.Bridge.leadMinor_cell L (ptMat p) U hL hU' l hl] at h1
    rw [DminN, dif_pos (Nat.lt_succ_of_le hl)]
    exact h1.symm
  have hiff : ∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p) := by
    intro l hl
    by_cases hl' : l ≤ D.R.rS + 1
    · have h2 := minor_ne_iff p.1 hp 0 l hl
      rw [zero_add] at h2
      rw [Ne, ← Complex.normSq_eq_zero, key l hl', Complex.normSq_eq_zero]
      exact h2
    · rw [DminN, dif_neg (by omega)]
      exact ⟨fun h0 => absurd rfl h0, fun hm => absurd (e1 l hm).2 hl'⟩
  have hG0 : 0 < Gf D.R.k D.R.rS z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS z z' hz hz' hT hT' γ hU) (Ne.symm hG)
  refine ⟨hiff, e2, fun l hl => e1 l hl, e3 fun h0 => ?_, ?_, hG0, ?_, fun b C C₂ hb hC hC2 => ?_⟩
  · rw [h0] at hsum
    simp at hsum
  · simp [DminN, Formalism.QuantumDeterminants.Dmin]
  · rw [DminN, dif_pos (by omega), ← Complex.normSq_eq_norm_sq]
    have := mul_nonneg (mul_pos hT hT').le
      (Complex.normSq_nonneg (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' γ ⟨D.R.rS, by omega⟩))
    exact sub_le_self _ this
  · have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have ex : ∀ x : ℝ, 0 ≤ x → 0 ≤ C * x ∧ C * x ≤ C₂ * x := fun x hx =>
      ⟨mul_nonneg hC hx, mul_le_mul_of_nonneg_right hC2 hx⟩
    obtain ⟨p1, p2⟩ := list_prod (ptBlockEnds p) (fun l => max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹)
      (fun l hl => one_le_max_inv _ (norm_pos_iff.2 ((hiff l (e1 l hl).1).2 hl))) _ _ (ex _ hm).1 (ex _ hm).2
    have g := one_le_max_inv _ hG0
    have a1 := Real.one_le_rpow hb (ex _ (pow_nonneg hm 4)).1
    have a2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ (pow_nonneg hm 4)).2
    have g1 := Real.one_le_rpow g (ex _ (pow_nonneg hm 2)).1
    have g2 := Real.rpow_le_rpow_of_exponent_le g (ex _ (pow_nonneg hm 2)).2
    have c1 := Real.one_le_rpow hb (ex _ hm).1
    have c2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ hm).2
    have f := one_le_foldr ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
    have q1 := one_le_mul_of_one_le_of_one_le c1 f
    have q2 := mul_le_mul_of_nonneg_right c2 (zero_le_one.trans f)
    refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 g1) p1, ?_,
      Real.one_le_rpow q1 (ex _ (pow_nonneg hr 3)).1, ?_⟩
    · exact mul_le_mul (mul_le_mul a2 g2 (by linarith) (by linarith)) p2 (by linarith)
        (mul_nonneg (by linarith) (by linarith))
    · exact (Real.rpow_le_rpow (by linarith) q2 (ex _ (pow_nonneg hr 3)).1).trans
        (Real.rpow_le_rpow_of_exponent_le (q1.trans q2) (ex _ (pow_nonneg hr 3)).2)

end GlobalTheory.Amp.PtMinor
