import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix

namespace GlobalTheory

theorem hform_exists_unit_value {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] (τ : R →+* R) (H H' : Matrix n n R) (p w v : R) (hinv : ∀ a, τ (τ a) = a)
    (hw : w + τ w = 1) (hwv : (w - τ w) * v = 1) (hH : Formalism.UG.cT τ H = H) (hHH' : H * H' = 1)
    (hloc : ∀ a, τ a = a → (¬ ∃ s, a = p * s) → IsUnit a) (hp : ¬ ∃ s, p * s = 1) :
    ∃ e : n → R, IsUnit (Formalism.UG.hform τ H e e) := by
  have hHij : ∀ i j, τ (H j i) = H i j := fun i j => by
    have := congrFun (congrFun hH i) j
    simpa [Formalism.UG.cT] using this
  have hsymm : ∀ x y, Formalism.UG.hform τ H y x = τ (Formalism.UG.hform τ H x y) := by
    intro x y
    simp only [Formalism.UG.hform, map_sum, map_mul, hinv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hHij]; ring
  have haddL : ∀ x y z, Formalism.UG.hform τ H (x + y) z = Formalism.UG.hform τ H x z + Formalism.UG.hform τ H y z := by
    intro x y z
    simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have haddR : ∀ x y z, Formalism.UG.hform τ H z (x + y) = Formalism.UG.hform τ H z x + Formalism.UG.hform τ H z y := by
    intro x y z
    simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsmulL : ∀ (c : R) x y, Formalism.UG.hform τ H (c • x) y = τ c * Formalism.UG.hform τ H x y := by
    intro c x y
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsmulR : ∀ (c : R) x y, Formalism.UG.hform τ H x (c • y) = c * Formalism.UG.hform τ H x y := by
    intro c x y
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  by_contra hne
  push_neg at hne

  have hdiag : ∀ e, ∃ s, Formalism.UG.hform τ H e e = p * s := by
    intro e
    by_contra hns
    exact hne e (hloc _ (hsymm e e).symm hns)

  have hall : ∀ x y, ∃ s, Formalism.UG.hform τ H x y = p * s := by
    intro x y
    have e1 : Formalism.UG.hform τ H x y + τ (Formalism.UG.hform τ H x y) =
        Formalism.UG.hform τ H (x + y) (x + y) - Formalism.UG.hform τ H x x - Formalism.UG.hform τ H y y := by
      simp only [haddL, haddR]
      rw [hsymm x y]; ring
    have e2 : τ w * Formalism.UG.hform τ H x y + w * τ (Formalism.UG.hform τ H x y) =
        Formalism.UG.hform τ H (w • x + y) (w • x + y) - Formalism.UG.hform τ H (w • x) (w • x)
        - Formalism.UG.hform τ H y y := by
      simp only [haddL, haddR, hsmulL, hsmulR]
      rw [hsymm x y]; ring
    obtain ⟨a1, ha1⟩ := hdiag (x + y)
    obtain ⟨a2, ha2⟩ := hdiag x
    obtain ⟨a3, ha3⟩ := hdiag y
    obtain ⟨b1, hb1⟩ := hdiag (w • x + y)
    obtain ⟨b2, hb2⟩ := hdiag (w • x)
    have key : Formalism.UG.hform τ H x y = v * (w * (Formalism.UG.hform τ H x y + τ (Formalism.UG.hform τ H x y))
        - (τ w * Formalism.UG.hform τ H x y + w * τ (Formalism.UG.hform τ H x y))) := by
      have : w * (Formalism.UG.hform τ H x y + τ (Formalism.UG.hform τ H x y))
          - (τ w * Formalism.UG.hform τ H x y + w * τ (Formalism.UG.hform τ H x y))
          = (w - τ w) * Formalism.UG.hform τ H x y := by ring
      rw [this, ← mul_assoc, mul_comm v, hwv, one_mul]
    refine ⟨v * (w * (a1 - a2 - a3) - (b1 - b2 - a3)), ?_⟩
    rw [key, e1, e2, ha1, ha2, ha3, hb1, hb2]; ring
  have hHp : ∀ i j, ∃ s, H i j = p * s := by
    intro i j
    have : Formalism.UG.hform τ H (Pi.single i 1) (Pi.single j 1) = H i j := by
      simp [Formalism.UG.hform, Pi.single_apply]
    rw [← this]; exact hall _ _
  choose c hc using hHp
  obtain ⟨i0⟩ := ‹Nonempty n›
  apply hp
  refine ⟨∑ k, c i0 k * H' k i0, ?_⟩
  have h1 := congrFun (congrFun hHH' i0) i0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [← h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc]; ring

end GlobalTheory
