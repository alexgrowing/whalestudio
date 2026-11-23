import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

theorem zero_ne_last (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h2
  omega

def sgd (d : ℂ) : ℂ := ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)

theorem sgd_sq (d : ℂ) (hd : 1 < ‖d‖) : sgd d * sgd d = d * conj d - 1 := by
  have hx : 0 ≤ Complex.normSq d - 1 := by
    have h1 : 1 < Complex.normSq d := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg d]
    linarith
  unfold sgd
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_one]

theorem star_sgd (d : ℂ) : star (sgd d) = sgd d := by
  unfold sgd
  exact Complex.conj_ofReal _

section entries
variable (hk : 1 ≤ k) (d : ℂ)
include hk

theorem character_first_entry : mud k d 0 0 = -conj d := by
  unfold mud
  simp
theorem character_last_entry : mud k d (Fin.last k) 0 = -sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.1.symm), if_pos ⟨rfl, rfl⟩]
theorem mud0L : mud k d 0 (Fin.last k) = sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1), if_pos ⟨rfl, rfl⟩]
theorem mudLL : mud k d (Fin.last k) (Fin.last k) = d := by
  have h0 := zero_ne_last hk
  unfold mud
  rw [if_neg (fun h => h0 h.1.symm), if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1.symm),
    if_pos ⟨rfl, rfl⟩]

theorem mud_col {l j : Fin (k + 1)} (hj0 : j ≠ 0) (hjL : j ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hj0 h.2), if_neg (fun h => hj0 h.2), if_neg (fun h => hjL h.2),
    if_neg (fun h => hjL h.2)]

theorem mud_row {l j : Fin (k + 1)} (hl0 : l ≠ 0) (hlL : l ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hl0 h.1), if_neg (fun h => hlL h.1), if_neg (fun h => hl0 h.1),
    if_neg (fun h => hlL h.1)]

theorem sum_two {f : Fin (k + 1) → ℂ} (hf : ∀ l, l ≠ 0 → l ≠ Fin.last k → f l = 0) :
    ∑ l, f l = f 0 + f (Fin.last k) := Finset.sum_eq_add 0 (Fin.last k) (zero_ne_last hk) (fun c _ hc => hf c hc.1 hc.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)

theorem mul_mud_col (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (k + 1)} (hj0 : j ≠ 0)
    (hjL : j ≠ Fin.last k) : (P * mud k d) i j = P i j := by
  rw [Matrix.mul_apply]
  simp [mud_col hk d hj0 hjL]

theorem mul_mud_blk (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) (hj : j = 0 ∨ j = Fin.last k) :
    (P * mud k d) i j = P i 0 * mud k d 0 j + P i (Fin.last k) * mud k d (Fin.last k) j := by
  rw [Matrix.mul_apply]
  apply sum_two hk
  intro l hl0 hlL
  rw [mud_row hk d hl0 hlL, if_neg, mul_zero]
  rintro rfl
  rcases hj with h | h
  · exact hl0 h
  · exact hlL h

end entries

theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then (if i = Fin.last k then -1 else 1) else 0 := by
  unfold Hb
  rw [Matrix.diagonal_apply]

theorem mud_unitary (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d)ᴴ * Hb k * mud k d = Hb k := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  ext i j
  have hP : ∀ a b : Fin (k + 1), ((mud k d)ᴴ * Hb k) a b = star (mud k d b a) * (if b = Fin.last k then -1 else 1) := by
    intro a b; unfold Hb; rw [mul_diagonal, conjTranspose_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, hss,
        Complex.star_def]
      ring
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hi0]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def,
        Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, hss, Complex.star_def]
      linear_combination hs
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hP, mud_row hk d hj0 hjL, Hb_apply]
    by_cases hij : i = j
    · subst hij; simp [hjL]
    · rw [if_neg (Ne.symm hij), if_neg hij]; simp

theorem mud_conj_mul (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d).map (starRingEnd ℂ) * mud k d = 1 := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  have hc : ∀ a b : Fin (k + 1), ((mud k d).map (starRingEnd ℂ)) a b = conj (mud k d a b) := fun a b => rfl
  have hsc : conj (sgd d) = sgd d := hss
  ext i j
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hc, hc, one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, character_last_entry hk, if_true, map_neg, hsc, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, character_first_entry hk, if_neg h0L.symm, map_neg, hsc]
      ring
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hc, hc, one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, mudLL hk, if_neg h0L, if_neg h0L.symm, map_neg, hsc, Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, mud0L hk, if_true, map_neg, hsc]
      linear_combination -hs
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hc, mud_col hk d hj0 hjL, one_apply]
    split_ifs <;> simp

theorem herm_mulVec {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    herm H (A *ᵥ u) (A *ᵥ v) = herm (Aᴴ * H * A) u v := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem herm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) (u v : Fin n → ℂ) :
    herm H (a • u) (b • v) = a * conj b * herm H u v := by
  unfold herm
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem herm_mud_last (hk : 1 ≤ k) (d : ℂ) :
    herm (Hb k) (mud k d *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -d := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp [Pi.single_apply, Hb_apply, mudLL hk d]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wbE_smul {r : ℕ} (a : ℂ) (v : Fin (k + 1) → ℂ) : wbE k r (a • v) = a • wbE k r v := by
  funext i
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [wbE, h]

theorem bvec_wI {r : ℕ} (j : Fin (k + 1)) : bvec (wI k r j) = wbE k r (Pi.single j 1) := by
  funext i
  simp only [bvec, wI, wbE, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
