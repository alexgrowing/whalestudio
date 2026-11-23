import Mathlib
import Formalism.PeriodIntegrals.ScPiExists

noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

def sg (ε : Fin n → Bool) (j : Fin n) : ℂ := if ε j then 1 else -1

theorem star_sg (ε : Fin n → Bool) (j : Fin n) : star (sg ε j) = sg ε j := by
  unfold sg; split_ifs <;> simp

theorem hJ_eq_sum (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    hJ ε x y = ∑ j, star (x j) * (sg ε j * y j) := by
  simp [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal, sg]

theorem hJ_conj (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  rw [hJ_eq_sum, hJ_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', star_mul', star_star, star_sg]; ring

theorem hJ_sub_left (ε : Fin n → Bool) (x x' y : Fin n → ℂ) :
    hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  simp only [hJ_eq_sum, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]

theorem hJ_sub_right (ε : Fin n → Bool) (x y y' : Fin n → ℂ) :
    hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp only [hJ_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ_eq_sum, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hJ_smul_right (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hJ_sum_smul_right (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ b, g b • m b) = ∑ b, g b * hJ ε x (m b) := by
  simp only [hJ_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring

theorem hJ_sum_smul_left (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, g a • m a) y = ∑ a, star (g a) * hJ ε (m a) y := by
  simp only [hJ_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring

theorem hJ_self (ε : Fin n → Bool) (x : Fin n → ℂ) :
    hJ ε x x = ((∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) : ℝ) : ℂ) := by
  rw [hJ_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  unfold sg
  split_ifs <;> simp

theorem hJ_self_re (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (hJ ε x x).re = ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) := by
  rw [hJ_self]; exact Complex.ofReal_re _

theorem exists_rel {ι κ : Type*} [Fintype ι] [Fintype κ] (v : κ → ι → ℂ)
    (h : Fintype.card ι < Fintype.card κ) : ∃ g : κ → ℂ, ∑ j, g j • v j = 0 ∧ ∃ j, g j ≠ 0 := by
  apply Fintype.not_linearIndependent_iff.mp
  intro hli
  have := hli.fintype_card_le_finrank
  simp at this
  omega

theorem exists_perp (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (u : ι → Fin n → ℂ)
    (h : Fintype.card ι < n) : ∃ y : Fin n → ℂ, y ≠ 0 ∧ ∀ i, hJ ε (u i) y = 0 := by
  obtain ⟨g, hg, j, hj⟩ := exists_rel (fun (j : Fin n) (i : ι) => star (u i j) * sg ε j)
    (by simpa using h)
  refine ⟨g, fun h0 => hj (congrFun h0 j), fun i => ?_⟩
  have := congrFun hg i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [hJ_eq_sum, ← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem re_star_mul_mul (a b : ℂ) : (star a * (a * b)).re = Complex.normSq a * b.re := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring

end PI.ScPiFrameW
