import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.DMComm

variable {n : ℕ}

theorem barM_single (ε : Fin n → Bool) (x : Mode ε) :
    barM ε (Matrix.single x.1.2 x.1.1 1) = Matrix.single x.1.1 x.1.2 1 := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := x
  ext i j
  simp only [barM, Matrix.single_apply]
  by_cases h : b = j ∧ a = i
  · obtain ⟨rfl, rfl⟩ := h
    simp only at ha hb
    simp [sg, ha, hb]
  · have h' : ¬ (a = i ∧ b = j) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem dM_inl (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inl (i, j))) = (if j = x.1.1 then X (Sum.inl (i, x.1.2)) else 0)
      - (if i = x.1.2 then X (Sum.inl (x.1.1, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl, Finset.sum_sub_distrib]
  congr 1
  · by_cases h : j = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem dM_inr (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inr (i, j))) = (if j = x.1.2 then X (Sum.inr (i, x.1.1)) else 0)
      - (if i = x.1.1 then X (Sum.inr (x.1.2, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inr, Finset.sum_sub_distrib, barM_single]
  congr 1
  · by_cases h : j = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem mode_ne (ε : Fin n → Bool) (w x : Mode ε) : x.1.2 ≠ w.1.1 := by
  intro h
  have h1 := x.2.2
  rw [h, w.2.1] at h1
  exact absurd h1 (by simp)

theorem dM_comm_X (ε : Fin n → Bool) (w x : Mode ε) (v : (Fin n × Fin n) ⊕ (Fin n × Fin n)) :
    dM ε w (dM ε x (X v)) = dM ε x (dM ε w (X v)) := by
  have h1 := mode_ne ε w x
  have h2 := mode_ne ε x w
  have h3 := h1.symm
  have h4 := h2.symm
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [dM_inl, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all
  · simp only [dM_inr, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all

theorem dM_comm : GlobalTheory.PsCo.Cw2a.T_dM_comm := by
  intro n ε w x P
  have h : ⁅dM ε w, dM ε x⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, dM_comm_X, sub_self]
    rfl
  have h2 := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

end GlobalTheory.PsCo.DMComm
