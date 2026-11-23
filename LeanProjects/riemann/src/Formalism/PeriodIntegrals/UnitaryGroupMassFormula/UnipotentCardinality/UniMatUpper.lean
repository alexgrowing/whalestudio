import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

namespace PI.GGCardUniWork

open Finset Matrix Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

abbrev Pairs (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def uniMat (f : Pairs k → F) : Matrix (Fin k) (Fin k) F :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

theorem uniMat_upper (f : Pairs k → F) : (uniMat f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [uniMat, ne_of_gt hji, not_lt.mpr hji.le]

theorem uniMat_det (f : Pairs k → F) : (uniMat f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (uniMat_upper f)]
  simp [uniMat]

noncomputable def uniGL (f : Pairs k → F) : GL (Fin k) F :=
  GeneralLinearGroup.mkOfDetNeZero (uniMat f) (by rw [uniMat_det]; exact one_ne_zero)

theorem uniGL_coe (f : Pairs k → F) : ((uniGL f : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = uniMat f := rfl

theorem isUni_uniGL (f : Pairs k → F) : IsUni k (uniGL f) := by
  unfold IsUni
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · simp [uniGL_coe, uniMat]
  · simp [uniGL_coe, uniMat, ne_of_gt h, not_lt.mpr h.le]

noncomputable def uniEquiv : {x : GL (Fin k) F // IsUni k x} ≃ (Pairs k → F) where
  toFun x p := (x.1 : Matrix (Fin k) (Fin k) F) p.1.1 p.1.2
  invFun f := ⟨uniGL f, isUni_uniGL f⟩
  left_inv x := by
    obtain ⟨x, hd, hl⟩ := x
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    simp only [uniGL_coe, uniMat]
    by_cases h : i = j
    · subst h; simp [hd i]
    · by_cases h' : i < j
      · simp [h, h']
      · have : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
        simp [h, h', hl i j this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h1 : i ≠ j := ne_of_lt h
    simp [uniGL_coe, uniMat, h1, h]

theorem card_pairs (k : ℕ) : Fintype.card (Pairs k) = k * (k - 1) / 2 := by
  have hI : ∀ j : Fin k, (∑ i : Fin k, if i < j then 1 else 0) = (j : ℕ) := fun j => by
    rw [← Finset.card_filter]
    rw [show (Finset.univ.filter fun i : Fin k => i < j) = Finset.Iio j by ext i; simp]
    exact Fin.card_Iio j
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [hI]
  have h3 : ∑ j : Fin k, (j : ℕ) = ∑ j ∈ Finset.range k, j := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h3, Finset.sum_range_id]

theorem cardUni : CardUni := by
  intro F _ _ k
  unfold cardU
  rw [Nat.card_congr (uniEquiv (F := F) (k := k)), Nat.card_eq_fintype_card, Fintype.card_fun,
    card_pairs]

end PI.GGCardUniWork
