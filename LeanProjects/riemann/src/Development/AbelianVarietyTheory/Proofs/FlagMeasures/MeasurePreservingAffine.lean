import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped Classical

namespace GlobalTheory.LoopVol

theorem measurePreserving_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.det = 1) (b : ι → ℂ) :
    MeasurePreserving (fun c : ι → ℂ => M *ᵥ c + b) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' M).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_restrictScalars, LinearMap.det_toLin', hM, map_one]
  have hfun : (f : (ι → ℂ) → ι → ℂ) = fun c => M *ᵥ c := by
    funext c
    simp [f, Matrix.toLin'_apply]
  have hlin : MeasurePreserving (fun c : ι → ℂ => M *ᵥ c) volume volume := by
    rw [← hfun]
    refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  exact (measurePreserving_add_right volume b).comp hlin

variable {N : ℕ}

theorem ofRoots_eq (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2) (c : R → ℂ) (i j : Fin N) :
    ofRoots R c i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + ∑ q : R, if q.1 = (i, j) then c q else 0 := by
  simp only [ofRoots]
  by_cases h : (i, j) ∈ R
  · rw [dif_pos h, Matrix.one_apply_ne (hR _ h).ne, zero_add, Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro h'
      exact hq (Subtype.ext h')
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dif_neg h, Finset.sum_eq_zero, add_zero, Matrix.one_apply]
    intro q _
    rw [if_neg]
    intro h'
    apply h
    rw [← h']
    exact q.2

theorem det_two_sided (R : Finset (Fin N × Fin N)) (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a)
    (hb : IsUpUni b) : (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2).det = 1 := by
  let key : R → Fin N ×ₗ (Fin N)ᵒᵈ := fun q => toLex (q.1.1, OrderDual.toDual q.1.2)
  have hinj : Function.Injective key := by
    intro x y h
    simp only [key, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  let e := Equiv.ofInjective key hinj
  rw [← Matrix.det_reindex_self e, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, (ha _ _).2 rfl,
      (hb _ _).2 rfl, mul_one]
  · intro i j hlt
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    have hk : key (e.symm j) < key (e.symm i) := by
      simp only [e, Equiv.apply_ofInjective_symm]
      exact hlt
    simp only [key, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at hk
    rcases hk with h1 | ⟨-, h2⟩
    · rw [(ha _ _).1 h1, zero_mul]
    · rw [(hb _ _).1 h2, mul_zero]

theorem measurePreserving_mul (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a) (hb : IsUpUni b) :
    MeasurePreserving (fun (c : R → ℂ) (q : R) => (a * ofRoots R c * b) q.1.1 q.1.2) volume volume := by
  have hent : ∀ (c : R → ℂ) (x y : Fin N),
      (a * ofRoots R c * b) x y = ∑ q : R, a x q.1.1 * b q.1.2 y * c q + (a * b) x y := by
    intro c x y
    have hO : ofRoots R c = 1 + ∑ q : R, c q • Matrix.of (fun i j => if q.1 = (i, j) then (1 : ℂ) else 0) := by
      ext i j
      rw [ofRoots_eq R hR c i j, Matrix.add_apply, Matrix.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [hO, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, add_comm, Finset.mul_sum,
      Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm (c q)]
    congr 1
    simp [Matrix.mul_apply, Prod.ext_iff, ite_and]
  have h := measurePreserving_affine (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2)
    (det_two_sided R a b ha hb) (fun q : R => (a * b) q.1.1 q.1.2)
  convert h using 1
  funext c q
  simp only [hent, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem measurePreserving_mul_pi {ι : Type*} [Fintype ι] (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : ι → Matrix (Fin N) (Fin N) ℂ) (ha : ∀ v, IsUpUni (a v)) (hb : ∀ v, IsUpUni (b v)) :
    MeasurePreserving (fun (c : ι → R → ℂ) (v : ι) (q : R) => (a v * ofRoots R (c v) * b v) q.1.1 q.1.2)
      volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun v =>
    measurePreserving_mul R hR (a v) (b v) (ha v) (hb v)

end GlobalTheory.LoopVol

end
