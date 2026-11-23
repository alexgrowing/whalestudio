import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetComplexification

namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable def pCoord (p q : ℕ) : (Fin p → Fin q → ℂ) →+ (PIx p q → ℂ) where
  toFun C := fun ab => pY C ab.1.1 ab.1.2
  map_zero' := by
    funext ⟨⟨a, b⟩, h⟩
    cases a <;> cases b <;> simp [pY, pOf]
  map_add' B C := by funext ab; simp [pY_add]

theorem pCoord_apply {p q : ℕ} (C : Fin p → Fin q → ℂ) (ab : PIx p q) :
    pCoord p q C ab = pY C ab.1.1 ab.1.2 := rfl

private lemma pY_inl_inr {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inl i) (Sum.inr j) = C i j := by
  simp [pY, pOf]

private lemma pY_inr_inl {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inr j) (Sum.inl i) = star (C i j) := by
  simp [pY, pOf]

private lemma pY_eq_zero_of_sameBlock {p q : ℕ} (C : Fin p → Fin q → ℂ) (a b : Ix p q)
    (h : sameBlock a b) : pY C a b = 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, pY, pOf]

private lemma not_sameBlock_inl_inr {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inl i : Ix p q) (Sum.inr j) := by
  simp [sameBlock]

private lemma not_sameBlock_inr_inl {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inr j : Ix p q) (Sum.inl i) := by
  simp [sameBlock]

theorem det_sinhc_eq_polarJacobian (p q : ℕ) (Y : Mat p q)
    (hY : ∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) :
    LinearMap.det (sP Y) = polJ Y := by

  set M : Matrix (PIx p q) (PIx p q) ℂ :=
    (sinhcAd Y).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hM

  have hj : ∀ (t : ℝ) (x : Fin p → Fin q → ℂ), pCoord p q (t • x) = (t : ℂ) • pCoord p q x := by
    intro t x
    funext ab
    simp only [pCoord_apply, pY_smul, Pi.smul_apply, Matrix.smul_apply, Complex.real_smul,
      smul_eq_mul]

  have hspan : ∀ w : PIx p q → ℂ, ∃ a b : Fin p → Fin q → ℂ,
      w = pCoord p q a + Complex.I • pCoord p q b := by
    intro w
    let u : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
    let v : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
    refine ⟨fun i j => (u i j + star (v i j)) / 2,
      fun i j => -Complex.I * (u i j - star (v i j)) / 2, ?_⟩
    funext ⟨⟨a, b⟩, h⟩
    rcases a with i | j <;> rcases b with j' | i'
    · exact absurd (by simp [sameBlock]) h
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inl_inr]
      apply Complex.ext <;> simp [u] <;> ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inr_inl]
      apply Complex.ext <;> simp [v] <;> ring
    · exact absurd (by simp [sameBlock]) h

  have hinj : ∀ a b : Fin p → Fin q → ℂ,
      pCoord p q a + Complex.I • pCoord p q b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 : ∀ i j, a i j + Complex.I * b i j = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
      simpa [pCoord_apply, pY_inl_inr] using this
    have h2 : ∀ i j, star (a i j) + Complex.I * star (b i j) = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
      simpa [pCoord_apply, pY_inr_inl] using this
    have hre : ∀ i j, a i j = 0 ∧ b i j = 0 := by
      intro i j
      have e1 := congrArg Complex.re (h1 i j)
      have e2 := congrArg Complex.im (h1 i j)
      have e3 := congrArg Complex.re (h2 i j)
      have e4 := congrArg Complex.im (h2 i j)
      simp at e1 e2 e3 e4
      constructor <;> apply Complex.ext <;> simp <;> linarith
    exact ⟨funext fun i => funext fun j => (hre i j).1,
      funext fun i => funext fun j => (hre i j).2⟩

  have hS : ∀ x, Matrix.toLin' M (pCoord p q x) = pCoord p q (sP Y x) := by
    intro x
    funext ab
    rw [Matrix.toLin'_apply, pCoord_apply, ← hY x]
    simp only [sAd, Matrix.of_apply, Matrix.mulVec, dotProduct, vecM, hM,
      Matrix.submatrix_apply, pCoord_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun cd : Ix p q × Ix p q => ¬ sameBlock cd.1 cd.2)]
    have hz : ∑ cd : {cd : Ix p q × Ix p q // ¬ ¬ sameBlock cd.1 cd.2},
        sinhcAd Y (ab.1.1, ab.1.2) cd.1 * pY x cd.1.1 cd.1.2 = 0 := by
      apply Finset.sum_eq_zero
      intro cd _
      rw [pY_eq_zero_of_sameBlock x _ _ (not_not.mp cd.2), mul_zero]
    rw [hz, add_zero]
  have key := det_complexification (Fin p → Fin q → ℂ) (PIx p q → ℂ) (pCoord p q) (sP Y)
    (Matrix.toLin' M) hj hspan hinj hS
  rw [LinearMap.det_toLin'] at key
  unfold polJ
  rw [← hM, key, Complex.ofReal_re]

end GlobalTheory.PolarU
