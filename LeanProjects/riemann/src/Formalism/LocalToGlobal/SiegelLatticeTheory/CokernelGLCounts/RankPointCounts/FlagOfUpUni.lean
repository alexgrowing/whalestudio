import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfCoefficients

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Uni

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji (not_lt.1 hk)), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · simp

theorem loUni_iff_ct {A : Matrix (Fin N) (Fin N) K} [StarRing K] : IsLoUni A ↔ IsUpUni Aᴴ := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · rw [conjTranspose_apply, (h j i).1 hji, star_zero]
    · subst hij; rw [conjTranspose_apply, (h i i).2 rfl, star_one]
  · intro h i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have := (h j i).1 hij
      rw [conjTranspose_apply] at this
      exact star_eq_zero.1 this
    · subst hij
      have := (h i i).2 rfl
      rw [conjTranspose_apply] at this
      rw [← star_star (A i i), this, star_one]

theorem upUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem loUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem upUni_inv {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : IsUpUni A⁻¹ := by
  have hdet : IsUnit A.det := by rw [upUni_det h]; exact isUnit_one
  have hbt : A.BlockTriangular id := fun i j hij => (h i j).1 hij
  haveI := A.invertibleOfIsUnitDet hdet
  have hbt' : A⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  intro i j
  refine ⟨fun hji => hbt' hji, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [(h i k).1 hlt, zero_mul]
    · rw [hbt' hgt, mul_zero]
  · simp

theorem loUni_mul {A B : Matrix (Fin N) (Fin N) K} [StarRing K] (hA : IsLoUni A) (hB : IsLoUni B) :
    IsLoUni (A * B) := by
  rw [loUni_iff_ct, conjTranspose_mul]
  exact upUni_mul (loUni_iff_ct.1 hB) (loUni_iff_ct.1 hA)

theorem loUni_inv {A : Matrix (Fin N) (Fin N) K} [StarRing K] (h : IsLoUni A) : IsLoUni A⁻¹ := by
  rw [loUni_iff_ct, conjTranspose_nonsing_inv]
  exact upUni_inv (loUni_iff_ct.1 h)

theorem upUni_last {r : ℕ} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni A) (c : Fin (r + 1)) :
    A (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  by_cases hc : c = Fin.last r
  · subst hc; rw [if_pos rfl]; exact (h _ _).2 rfl
  · rw [if_neg hc]
    exact (h _ _).1 (lt_of_le_of_ne (Fin.le_last c) hc)

end Uni

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem flag_of_upUni (F : FlagG S r T) (g : S.V →ₗ[E] S.V) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : IsUpUni N) (hg : ∀ b, g (F.fvec b) = ∑ c, N c b • F.fvec c) :
    (∀ j, ∀ x ∈ F.Xa (j + 1), g x - x ∈ F.Xa j) ∧ g F.z - F.z ∈ F.X := by
  have hdiff : ∀ b, g (F.fvec b) - F.fvec b = ∑ c ∈ Finset.univ.filter (· < b), N c b • F.fvec c := by
    intro b
    rw [hg b, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < b)]
    have h2 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < b), N c b • F.fvec c = F.fvec b := by
      rw [Finset.sum_eq_single b]
      · rw [(hN b b).2 rfl, one_smul]
      · intro c hc hcb
        have : b < c := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) (Ne.symm hcb)
        rw [(hN c b).1 this, zero_smul]
      · intro hb; exfalso; apply hb; simp
    rw [h2]; abel
  have he : ∀ a : Fin r, g (F.e a) - F.e a ∈ F.Xa a := by
    intro a
    have := hdiff (Fin.castSucc a)
    simp only [FlagG.fvec, Fin.snoc_castSucc] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc' : c < Fin.castSucc a := (Finset.mem_filter.1 hc).2
    have hcl : c ≠ Fin.last r := ne_of_lt (lt_trans hc' (Fin.castSucc_lt_last a))
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', by simpa using hc', rfl⟩
  refine ⟨fun j x hx => ?_, ?_⟩
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have ha' : (a : ℕ) < j + 1 := ha
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i, by show (i : ℕ) < j; have : (i : ℕ) < a := hi; omega, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
  · have := hdiff (Fin.last r)
    simp only [FlagG.fvec, Fin.snoc_last] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hcl : c ≠ Fin.last r := ne_of_lt (Finset.mem_filter.1 hc).2
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', rfl⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
