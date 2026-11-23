import Mathlib
import Formalism.PieriBlockIdeals.StatementLW

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

theorem shiftBound_holds : KapBound := by
  intro ι _ σ l h kap s hl hs hd i
  have : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun x => |kap x|)
  have hL : (2 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
  have h1 := hd (σ.symm j)
  have h2 := hs (σ.symm j)
  rw [Equiv.apply_symm_apply] at h1
  have h3 := abs_le.mp (hj (σ.symm j))
  have key : ((l : ℤ) - 1) * |kap j| ≤ (h : ℤ) := by
    rcases le_or_gt 0 (kap j) with hk | hk
    · rw [abs_of_nonneg hk] at h3 ⊢
      have e : ((l : ℤ) - 1) * kap j = (l : ℤ) * kap j - kap j := by ring
      rw [e]
      linarith [h1.2, h2.1, h3.2]
    · rw [abs_of_neg hk] at h3 ⊢
      have e : ((l : ℤ) - 1) * -kap j = -((l : ℤ) * kap j) + kap j := by ring
      rw [e]
      linarith [h1.1, h2.2, h3.1]
  have h4 : ((l : ℤ) - 1) * |kap i| ≤ ((l : ℤ) - 1) * |kap j| :=
    mul_le_mul_of_nonneg_left (hj i) (by linarith)
  exact le_trans h4 key

theorem lw_det_block {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (s : m) (hs : ∀ j, b j = b s → j = s) :
    (M.toSquareBlock b (b s)).det = M s s := by
  let _ : Unique {a // b a = b s} :=
    { default := ⟨s, rfl⟩
      uniq := fun j => Subtype.ext (hs j.1 j.2) }
  rw [Matrix.det_unique]
  rfl

theorem lw_det_inj {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (hM : M.BlockTriangular b) (hb : Function.Injective b) :
    M.det = ∏ i, M i i := by
  rw [Matrix.BlockTriangular.det hM, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun i _ => lw_det_block M b i (fun j hj => hb hj))
  · intro x _ y _ hxy
    exact hb hxy

theorem charpolyDiagBlocks_holds : CharpolyBlocks := by
  intro K _ n M b S r hM hS hchar
  have hC : (Matrix.charmatrix M).BlockTriangular b := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    simp [hne, hM hij]
  have hdet : M.charpoly
      = ∏ a ∈ univ.image b, ((Matrix.charmatrix M).toSquareBlock b a).det :=
    Matrix.BlockTriangular.det hC
  have hdvd : ∏ s ∈ S, (X - C (M s s)) ∣ M.charpoly := by
    rw [hdet]
    have h1 : ∏ s ∈ S, (X - C (M s s))
        = ∏ a ∈ S.image b, ((Matrix.charmatrix M).toSquareBlock b a).det := by
      rw [Finset.prod_image]
      · refine Finset.prod_congr rfl (fun s hs => ?_)
        rw [lw_det_block _ b s (hS s hs), Matrix.charmatrix_apply_eq]
      · intro x hx y _ hxy
        exact (hS x hx y hxy.symm).symm
    rw [h1]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.image_subset_image (Finset.subset_univ S))
  have hne : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hroots := Polynomial.roots.le_of_dvd hne hdvd
  have e1 : ∏ s ∈ S, (X - C (M s s))
      = (Multiset.map (fun a => X - C a) (S.val.map (fun s => M s s))).prod := by
    rw [Multiset.map_map]
    rfl
  have e2 : ∏ u, (X - C (r u))
      = (Multiset.map (fun a => X - C a) ((Finset.univ : Finset (Fin n)).val.map r)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [e1, Polynomial.roots_multiset_prod_X_sub_C, hchar, e2,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact hroots

end Formalism.CohomologicalDescent
