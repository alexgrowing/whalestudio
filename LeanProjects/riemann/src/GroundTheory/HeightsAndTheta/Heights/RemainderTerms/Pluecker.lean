import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Matrix Finset

open scoped ComplexOrder

noncomputable section

namespace Elem

variable {R : Type*} [CommRing R] {κ : Type*}

def subsetCols {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) : κ :=
  ((S.1.equivFinOfCardEq S.2).symm i : κ)

theorem subsetCols_injective {p : ℕ} (S : {s : Finset κ // s.card = p}) :
    Function.Injective (subsetCols S) := by
  intro i j h
  exact (S.1.equivFinOfCardEq S.2).symm.injective (Subtype.ext h)

theorem subsetCols_mem {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) :
    subsetCols S i ∈ S.1 :=
  ((S.1.equivFinOfCardEq S.2).symm i).2

theorem exists_subsetCols_eq {p : ℕ} (S : {s : Finset κ // s.card = p}) {k : κ}
    (hk : k ∈ S.1) : ∃ i, subsetCols S i = k :=
  ⟨S.1.equivFinOfCardEq S.2 ⟨k, hk⟩, by simp [subsetCols]⟩

theorem det_mul_expand [Fintype κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ φ : Fin p → κ, (A.submatrix id φ).det * ∏ i, B (φ i) i := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib]
  ring

theorem det_submatrix_eq_zero_of_not_injective {p : ℕ} (A : Matrix (Fin p) κ R)
    (φ : Fin p → κ) (h : ¬ Function.Injective φ) : (A.submatrix id φ).det = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

theorem cauchyBinet [Fintype κ] [DecidableEq κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det := by
  rw [det_mul_expand]
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun φ _ h => by
        by_contra hφ
        exact h (by rw [det_submatrix_eq_zero_of_not_injective A φ hφ, zero_mul]))]
  have hpairs : ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det =
      ∑ x : {s : Finset κ // s.card = p} × Equiv.Perm (Fin p),
        (A.submatrix id (subsetCols x.1 ∘ x.2)).det * ∏ i, B (subsetCols x.1 (x.2 i)) i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [det_apply' (B.submatrix _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have : A.submatrix id (subsetCols S ∘ π) =
        (A.submatrix id (subsetCols S)).submatrix id π := rfl
    rw [this, det_permute']
    simp only [submatrix_apply, id]
    ring
  rw [hpairs]
  symm
  refine Finset.sum_bij (fun x _ => subsetCols x.1 ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (subsetCols_injective x.1).comp x.2.injective
  · rintro ⟨S, π⟩ _ ⟨T, π'⟩ _ hxy
    simp only at hxy
    have hST : S = T := by
      apply Subtype.ext
      ext k
      constructor
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq S hk
        have := congrFun hxy (π.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [this]
        exact subsetCols_mem T _
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq T hk
        have := congrFun hxy (π'.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [← this]
        exact subsetCols_mem S _
    subst hST
    have : π = π' := by
      ext i
      exact congrArg Fin.val (subsetCols_injective S (congrFun hxy i))
    rw [this]
  · intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    let S : {s : Finset κ // s.card = p} :=
      ⟨Finset.univ.image φ, by rw [Finset.card_image_of_injective _ hφ]; simp⟩
    let g : Fin p → Fin p := fun i =>
      S.1.equivFinOfCardEq S.2 ⟨φ i, Finset.mem_image_of_mem φ (Finset.mem_univ i)⟩
    have hg : Function.Injective g := by
      intro i j h
      have := (S.1.equivFinOfCardEq S.2).injective h
      exact hφ (congrArg Subtype.val this)
    refine ⟨(S, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)),
      Finset.mem_univ _, ?_⟩
    funext i
    simp [subsetCols, g, S]
  · intro x _
    rfl

end Elem

open Elem in

theorem PlueckerCauchyBinet.intersectionNumber_baseChange : PlueckerCauchyBinet.Statement := by
  intro p q Z
  set A := Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) Z with hAdef
  have hA : 1 + Z * Z.conjTranspose = A * A.conjTranspose := by
    rw [hAdef, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp
  rw [hA, cauchyBinet, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hB : A.conjTranspose.submatrix (subsetCols S) id =
      (A.submatrix id (subsetCols S)).conjTranspose := by
    ext i j; simp
  rw [hB, det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem PlueckerHadamard.intersectionNumber_baseChange : PlueckerHadamard.Statement := by
  intro p q Z hZ
  set H := 1 + Z * Z.conjTranspose with hHdef
  have hpsd : H.PosSemidef := Matrix.PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)
  have hH : H.IsHermitian := hpsd.isHermitian
  set ev := hH.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := hpsd.eigenvalues_nonneg
  have hdet : H.det = ((∏ i, ev i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]; push_cast; rfl
  have htrH : H.trace = ((p * (1 + q) : ℝ) : ℂ) := by
    have hZZ : (Z * Z.conjTranspose).trace = ((p * q : ℕ) : ℂ) := by
      simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
      have : ∀ i j, Z i j * (starRingEnd ℂ) (Z i j) = 1 := by
        intro i j
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hZ i j]
        simp
      simp [this]
    rw [hHdef, trace_add, trace_one, hZZ]
    push_cast
    simp
    ring
  have hsum : ∑ i, ev i = p * (1 + q) := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [htrH] at h1
    have : ((∑ i, ev i : ℝ) : ℂ) = ((p * (1 + q) : ℝ) : ℂ) := by
      rw [h1]; push_cast; rfl
    exact_mod_cast this
  rw [hdet, Complex.ofReal_re]
  push_cast
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hamgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (fun _ : Fin p => 1 / (p : ℝ)) ev (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => hev i)
    have hrhs : ∑ i, 1 / (p : ℝ) * ev i = 1 + q := by
      rw [← Finset.mul_sum, hsum]; field_simp
    rw [hrhs] at hamgm
    have hprod : ∏ i, ev i = (∏ i, ev i ^ (1 / (p : ℝ))) ^ p := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hev i), one_div_mul_cancel hp'.ne', Real.rpow_one]
    rw [hprod]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hev i) _) hamgm p

end

end RestTerms

end GroundTheory.Heights₂.Heights
