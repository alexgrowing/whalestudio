import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem re_corner_eq_zero (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (hx : x ∈ Nset k r) (hd : Dep k r (2 * r - 2 * a.val) (x - 1)) :
    (x (eI k r a) (esI k r a)).re = 0 := by
  have hsv : (esI k r a).val = 2 * r + k - a.val := rfl
  have hev : (eI k r a).val = a.val := rfl
  generalize esI k r a = s at *
  generalize eI k r a = e at *
  have ha := a.isLt

  have hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → i ≠ s → x i s = 0 := by
    intro i hi hne
    have h0 := hd i s (by
      simp only [pos]
      split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h0; exact h0
  have hss : x s s = 1 := by
    have h0 := hd s s (by simp only [pos]; split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0; exact h0
  have hU := congrFun (congrFun hx.1 s) s
  have hH : Hpk k r s s = 0 := by
    simp only [Hpk, Fin.ext_iff, and_true]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  rw [hH] at hU
  have key : ∀ i j : Fin (2 * r + k + 1), star (x i s) * Hpk k r i j * x j s =
      (if i = s ∧ j = e then x j s else 0) + (if i = e ∧ j = s then star (x i s) else 0) := by
    intro i j
    by_cases h1 : i = s ∧ j = e
    · rw [h1.1, h1.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r s e = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    by_cases h2 : i = e ∧ j = s
    · rw [h2.1, h2.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r e s = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    rw [if_neg h1, if_neg h2, add_zero]
    have hi : i = s ∨ i.val ≤ a.val ∨ x i s = 0 := by
      by_cases h : i = s
      · exact Or.inl h
      by_cases h' : i.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol i (by omega) h))
    have hj : j = s ∨ j.val ≤ a.val ∨ x j s = 0 := by
      by_cases h : j = s
      · exact Or.inl h
      by_cases h' : j.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol j (by omega) h))
    have hI : ∀ i : Fin (2 * r + k + 1), i = s ↔ i.val = 2 * r + k - a.val := fun i =>
      ⟨fun h => h ▸ hsv, fun h => Fin.ext (h.trans hsv.symm)⟩
    have hE : ∀ i : Fin (2 * r + k + 1), i = e ↔ i.val = a.val := fun i =>
      ⟨fun h => h ▸ hev, fun h => Fin.ext (h.trans hev.symm)⟩
    rw [hI, hE] at h1 h2
    rcases hi with hi | hi | hi
    · rcases hj with hj | hj | hj
      · subst hi; subst hj; simp [hH]
      · have : Hpk k r i j = 0 := by
          rw [hI] at hi
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · rcases hj with hj | hj | hj
      · have : Hpk k r i j = 0 := by
          rw [hI] at hj
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · have : Hpk k r i j = 0 := by
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · simp [hi]
  have hsum : (xᴴ * Hpk k r * x) s s = x e s + star (x e s) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [key, Finset.sum_add_distrib]
    simp [ite_and, hss]
  rw [hsum] at hU
  have := congrArg Complex.re hU
  simp at this
  linarith

end GlobalTheory.SnMass.VolN
