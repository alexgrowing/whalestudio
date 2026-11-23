import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterizationStatement

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.DNorm

def sw (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

variable {k r : ℕ}

lemma sw_val (i : Fin (2 * r + k + 1)) :
    (sw k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sw
  split_ifs <;> rfl

lemma sw_sw (i : Fin (2 * r + k + 1)) : sw k r (sw k r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  rw [sw_val, sw_val]
  split_ifs <;> omega

lemma sg_sw (i : Fin (2 * r + k + 1)) : sg k r (sw k r i) = sg k r i := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold sg
  split_ifs at hs <;> split_ifs <;> first | rfl | omega

lemma lev_sw (i : Fin (2 * r + k + 1)) : lev k r (sw k r i) + lev k r i = 2 * r := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold lev
  split_ifs at hs <;> split_ifs <;> omega

lemma hpk_apply (i j : Fin (2 * r + k + 1)) : Hpk k r i j = if j = sw k r i then sg k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold Hpk sg
  simp only [Fin.ext_iff]
  split_ifs at hs <;> split_ifs <;> first | rfl | omega

lemma wC_apply (i j : Fin (2 * r + k + 1)) : wC k r i j = if j = sw k r i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold wC bigCell
  simp only [esI, Matrix.one_apply, Fin.ext_iff, star_one, inv_one]
  split_ifs at hs <;> split_ifs <;> first | rfl | omega

private lemma wC_mul_apply (N : Mat k r) (i j : Fin (2 * r + k + 1)) : (wC k r * N) i j = N (sw k r i) j := by
  simp [Matrix.mul_apply, wC_apply]

private lemma mul_wC_apply (N : Mat k r) (i j : Fin (2 * r + k + 1)) : (N * wC k r) i j = N i (sw k r j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k r j)]
  · rw [wC_apply, if_pos (sw_sw j).symm, mul_one]
  · intro l _ hl
    rw [wC_apply, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, sw_sw])
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma conj_apply (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (wC k r * M * wC k r) i j = M (sw k r i) (sw k r j) := by
  rw [mul_wC_apply, wC_mul_apply]

private lemma mul_Hpk_apply' (N : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (N * Hpk k r) i j = N i (sw k r j) * sg k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k r j)]
  · rw [hpk_apply, if_pos (sw_sw j).symm, sg_sw]
  · intro l _ hl
    rw [hpk_apply, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, sw_sw])
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma Hpk_mul_apply' (N : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * N) i j = sg k r i * N (sw k r i) j := by
  simp [Matrix.mul_apply, hpk_apply]

lemma skew_iff (M : Mat k r) : Mᴴ * Hpk k r + Hpk k r * M = 0 ↔
    ∀ i j, star (M (sw k r j) i) * sg k r j + sg k r i * M (sw k r i) j = 0 := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.add_apply, Matrix.zero_apply, mul_Hpk_apply', Hpk_mul_apply', Matrix.conjTranspose_apply]

lemma skew_conj {M : Mat k r} (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    (wC k r * M * wC k r)ᴴ * Hpk k r + Hpk k r * (wC k r * M * wC k r) = 0 := by
  rw [skew_iff] at h ⊢
  intro i j
  have hij := h (sw k r i) (sw k r j)
  simp only [conj_apply, sw_sw, sg_sw] at hij ⊢
  exact hij

private lemma torD_apply_of_ne (x : Fin r → ℂ) {i j : Fin (2 * r + k + 1)} (h : i ≠ j) : torD k r x i j = 0 := by
  unfold torD
  exact Matrix.diagonal_apply_ne _ h

private lemma torD_sw_sw_eq_neg_star (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) :
    torD k r x (sw k r i) (sw k r i) = -star (torD k r x i i) := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  have e2 : 2 * r + k - (2 * r + k - i.val) = i.val := by omega
  unfold torD
  simp only [Matrix.diagonal_apply_eq]
  split_ifs at hs <;> split_ifs <;> (try simp only [hs, e2]) <;> (try simp only [star_neg, star_star, neg_neg, star_zero, neg_zero]) <;>
    first | rfl | omega

lemma skew_torD (x : Fin r → ℂ) : (torD k r x)ᴴ * Hpk k r + Hpk k r * torD k r x = 0 := by
  rw [skew_iff]
  intro i j
  by_cases h : j = sw k r i
  · subst h
    rw [sw_sw, sg_sw, torD_sw_sw_eq_neg_star]
    ring
  · have h' : sw k r j ≠ i := fun e => h (by rw [← e, sw_sw])
    have h'' : sw k r i ≠ j := fun e => h e.symm
    rw [torD_apply_of_ne x h', torD_apply_of_ne x h'']
    simp

lemma norm_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

lemma norm_um {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X : lieE S) :
    ∑ i, ∑ j, ‖um X i j‖ ^ 2 = ‖X‖ ^ 2 :=
  norm_unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))

private lemma norm_sq_torD_diag_eq (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) :
    ‖torD k r x i i‖ ^ 2 = (if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0) +
      (if h : (sw k r i).val < r then ‖x ⟨(sw k r i).val, h⟩‖ ^ 2 else 0) := by
  have hi := i.isLt
  have hs := sw_val (k := k) (r := r) i
  unfold torD
  rw [Matrix.diagonal_apply_eq]
  split_ifs at hs <;> split_ifs <;> (try simp only [hs]) <;> (try simp only [norm_neg, norm_star, norm_zero, add_zero, zero_add]) <;>
    first | rfl | omega | norm_num

lemma norm_torD (x : Fin r → ℂ) : ∑ i, ∑ j, ‖torD k r x i j‖ ^ 2 = 2 * ∑ a, ‖x a‖ ^ 2 := by
  have hoff : ∀ i j : Fin (2 * r + k + 1), i ≠ j → torD k r x i j = 0 := fun i j h => by
    unfold torD
    exact Matrix.diagonal_apply_ne _ h
  have h1 : ∀ i, ∑ j, ‖torD k r x i j‖ ^ 2 = ‖torD k r x i i‖ ^ 2 := fun i => by
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [hoff i j (Ne.symm hj), norm_zero]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [h1, norm_sq_torD_diag_eq, Finset.sum_add_distrib]
  have hsw : (∑ i : Fin (2 * r + k + 1), if h : (sw k r i).val < r then ‖x ⟨(sw k r i).val, h⟩‖ ^ 2 else 0) =
      ∑ i : Fin (2 * r + k + 1), if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0 :=
    Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun i => sw_sw i))
      (fun i : Fin (2 * r + k + 1) => if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0)
  have hG : (∑ i : Fin (2 * r + k + 1), if h : i.val < r then ‖x ⟨i.val, h⟩‖ ^ 2 else 0) =
      ∑ a, ‖x a‖ ^ 2 := by
    refine (Fin.sum_univ_eq_sum_range (fun n => if h : n < r then ‖x ⟨n, h⟩‖ ^ 2 else 0) _).trans ?_
    rw [show 2 * r + k + 1 = r + (r + k + 1) by ring, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (s := Finset.range (r + k + 1)) (fun n _ => dif_neg (by omega)), add_zero]
    refine (Fin.sum_univ_eq_sum_range (fun n => if h : n < r then ‖x ⟨n, h⟩‖ ^ 2 else 0) r).symm.trans ?_
    exact Finset.sum_congr rfl fun a _ => dif_pos a.isLt
  rw [hsw, hG]
  ring

theorem dchart_skew_norm : ∀ (k r : ℕ) (v : EE k r),
    ((dchart k r v)ᴴ * Hpk k r + Hpk k r * dchart k r v = 0) ∧
    (∑ i, ∑ j, ‖dchart k r v i j‖ ^ 2) =
      ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2 := by
  intro k r v
  obtain ⟨⟨X, X'⟩, ⟨x, Y⟩⟩ := v
  have hX := (GlobalTheory.CellDens.LieN.lieE_Nset k r (X : EuclideanSpace ℝ _)).1.1 X.2
  have hX' := (GlobalTheory.CellDens.LieN.lieE_Nset k r (X' : EuclideanSpace ℝ _)).1.1 X'.2
  have hY := (GlobalTheory.CellLieAlg.lie_entries k r (Y : EuclideanSpace ℝ _)).2.1.1 Y.2
  change (um X)ᴴ * Hpk k r + Hpk k r * um X = 0 ∧
    ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → um X i j = 0 at hX
  change (um X')ᴴ * Hpk k r + Hpk k r * um X' = 0 ∧
    ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → um X' i j = 0 at hX'
  change (um Y)ᴴ * Hpk k r + Hpk k r * um Y = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
    ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → um Y i j = 0 at hY
  show (-(wC k r * um X * wC k r) + torD k r x + um Y + um X')ᴴ * Hpk k r +
      Hpk k r * (-(wC k r * um X * wC k r) + torD k r x + um Y + um X') = 0 ∧
    (∑ i, ∑ j, ‖(-(wC k r * um X * wC k r) + torD k r x + um Y + um X') i j‖ ^ 2) =
      ‖X‖ ^ 2 + ‖X'‖ ^ 2 + 2 * (∑ a, ‖x a‖ ^ 2) + ‖Y‖ ^ 2
  refine ⟨?_, ?_⟩
  · have e : ∀ A T B C : Mat k r, (-A + T + B + C)ᴴ * Hpk k r + Hpk k r * (-A + T + B + C) =
        -(Aᴴ * Hpk k r + Hpk k r * A) + (Tᴴ * Hpk k r + Hpk k r * T) + (Bᴴ * Hpk k r + Hpk k r * B) +
          (Cᴴ * Hpk k r + Hpk k r * C) := by
      intro A T B C
      simp only [conjTranspose_add, conjTranspose_neg, add_mul, mul_add, neg_mul, mul_neg]
      abel
    rw [e, skew_conj hX.1, skew_torD x, hY.1, hX'.1]
    simp
  · have hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val ∧ i.val ≤ r + k → lev k r i = r := fun i h => by
      unfold lev
      rw [if_neg (by omega), if_pos h.2]
    have hToff : ∀ i j : Fin (2 * r + k + 1), i ≠ j → torD k r x i j = 0 := fun i j h => by
      unfold torD
      exact Matrix.diagonal_apply_ne _ h
    have hTmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val ∧ i.val ≤ r + k → torD k r x i i = 0 := fun i h => by
      unfold torD
      rw [Matrix.diagonal_apply_eq, dif_neg (by omega), dif_neg (by omega)]
    have hentry : ∀ i j, ‖(-(wC k r * um X * wC k r) + torD k r x + um Y + um X') i j‖ ^ 2 =
        ‖um X (sw k r i) (sw k r j)‖ ^ 2 + ‖um X' i j‖ ^ 2 + ‖torD k r x i j‖ ^ 2 + ‖um Y i j‖ ^ 2 := by
      intro i j
      simp only [Matrix.add_apply, Matrix.neg_apply, conj_apply]
      have li := lev_sw (k := k) (r := r) i
      have lj := lev_sw (k := k) (r := r) j
      rcases lt_trichotomy (lev k r j) (lev k r i) with h | h | h
      · have h1 : um X' i j = 0 := hX'.2 i j h.le
        have h2 : torD k r x i j = 0 := hToff i j (by rintro rfl; omega)
        have h3 : um Y i j = 0 := hY.2 i j (by
          rintro ⟨hi, hj⟩
          rw [hmid i hi, hmid j hj] at h
          omega)
        rw [h1, h2, h3]
        simp
      · have h0 : um X (sw k r i) (sw k r j) = 0 := hX.2 _ _ (by omega)
        have h1 : um X' i j = 0 := hX'.2 i j h.le
        rw [h0, h1]
        by_cases hm : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
        · have h2 : torD k r x i j = 0 := by
            by_cases e : i = j
            · subst e
              exact hTmid i hm.1
            · exact hToff i j e
          rw [h2]
          simp
        · rw [hY.2 i j hm]
          simp
      · have h0 : um X (sw k r i) (sw k r j) = 0 := hX.2 _ _ (by omega)
        have h2 : torD k r x i j = 0 := hToff i j (by rintro rfl; omega)
        have h3 : um Y i j = 0 := hY.2 i j (by
          rintro ⟨hi, hj⟩
          rw [hmid i hi, hmid j hj] at h
          omega)
        rw [h0, h2, h3]
        simp
    have hswX : ∑ i, ∑ j, ‖um X (sw k r i) (sw k r j)‖ ^ 2 = ∑ i, ∑ j, ‖um X i j‖ ^ 2 := by
      have h1 : ∀ i, ∑ j, ‖um X i (sw k r j)‖ ^ 2 = ∑ j, ‖um X i j‖ ^ 2 := fun i =>
        Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun j => sw_sw j)) (fun j => ‖um X i j‖ ^ 2)
      simp only [h1]
      exact Equiv.sum_comp (Function.Involutive.toPerm (sw k r) (fun j => sw_sw j))
        (fun i => ∑ j, ‖um X i j‖ ^ 2)
    simp only [hentry, Finset.sum_add_distrib]
    rw [hswX, norm_um, norm_um, norm_torD, norm_um]

end GlobalTheory.CellDens.DNorm
