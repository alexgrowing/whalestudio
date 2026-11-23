import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open Matrix
open PositivityTheory.Rg.BcB.F.Eig

namespace GlobalTheory.CompanionTheory.UMod

def op {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 P)

theorem op_apply {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    op P x = WithLp.toLp 2 (P *ᵥ x.ofLp) := by
  simp [op, Matrix.toLpLin_apply]

theorem op_mul {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ) : op (P * Q) = op P * op Q := by
  ext1 x
  simp [op_apply, Matrix.mulVec_mulVec]

theorem op_one {d : ℕ} : op (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext1 x
  simp [op_apply]

theorem op_pow {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) : op (P ^ k) = op P ^ k := by
  induction k with
  | zero => simp [op_one]
  | succ k ih => rw [pow_succ, pow_succ, op_mul, ih]

theorem trace_op {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ _ ((op P : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
      EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) = P.trace := by
  have : ((op P : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
      EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) = Matrix.toEuclideanLin P := rfl
  rw [this, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

theorem diagOp_eq {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ) :
    diagOp blk c = op (Matrix.diagonal fun j => c (blk j)) := rfl

def kron {B : Type} [Fintype B] {n : B → Type} (M : ∀ w, Matrix (n w) (n w) ℂ) :
    Matrix (∀ w, n w) (∀ w, n w) ℂ :=
  Matrix.of fun a b => ∏ w, M w (a w) (b w)

section Kron

variable {B : Type} [Fintype B] [DecidableEq B] {n : B → Type} [∀ w, Fintype (n w)]
  [∀ w, DecidableEq (n w)]

theorem kron_mul (M N : ∀ w, Matrix (n w) (n w) ℂ) :
    kron M * kron N = kron fun w => M w * N w := by
  ext a b
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]

theorem kron_one : kron (fun w => (1 : Matrix (n w) (n w) ℂ)) = 1 := by
  ext a b
  simp only [kron, Matrix.of_apply]
  by_cases h : a = b
  · subst h
    simp
  · obtain ⟨w, hw⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Matrix.one_apply_ne hw)

theorem kron_pow (M : ∀ w, Matrix (n w) (n w) ℂ) (k : ℕ) :
    kron M ^ k = kron fun w => M w ^ k := by
  induction k with
  | zero => simp [kron_one]
  | succ k ih => simp only [pow_succ, ih, kron_mul]

theorem trace_kron (M : ∀ w, Matrix (n w) (n w) ℂ) :
    (kron M).trace = ∏ w, (M w).trace := by
  simp only [Matrix.trace, Matrix.diag, kron, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

theorem kron_mulVec (M : ∀ w, Matrix (n w) (n w) ℂ) (a : ∀ w, n w → ℂ) (x : ∀ w, n w) :
    (kron M *ᵥ fun y => ∏ w, a w (y w)) x = ∏ w, (M w *ᵥ a w) (x w) := by
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]

end Kron

theorem transfer {ι J : Type} [Fintype J] [DecidableEq J] (b : J → ι) (A : Matrix J J ℂ)
    (hc : ∀ c : ι → ℂ, Commute A (Matrix.diagonal fun j => c (b j))) :
    ∃ (d : ℕ) (blk : Fin d → ι) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)),
      (∀ c, Commute u (diagOp blk c)) ∧
      (∀ (c : ι → ℂ) (k : ℕ), LinearMap.trace ℂ _ ((u ^ k * diagOp blk c :
          EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) =
        (A ^ k * Matrix.diagonal fun j => c (b j)).trace) ∧
      ∀ (i₀ : ι) (v : J → ℂ), v ≠ 0 → A *ᵥ v = v → (∀ j, v j ≠ 0 → b j = i₀) →
        ∃ v', v' ≠ 0 ∧ u v' = v' ∧ ∀ c, diagOp blk c v' = c i₀ • v' := by
  let e := Fintype.equivFin J
  let R := Matrix.reindexAlgEquiv ℂ ℂ e
  have hD : ∀ c : ι → ℂ, R (Matrix.diagonal fun j => c (b j)) =
      Matrix.diagonal fun j => c (b (e.symm j)) := by
    intro c
    ext i j
    simp [R, Matrix.reindexAlgEquiv_apply, Matrix.diagonal_apply]
  refine ⟨Fintype.card J, b ∘ e.symm, op (R A), ?_, ?_, ?_⟩
  · intro c
    have h := (hc c).eq
    have h2 := congrArg (fun Z => op (R Z)) h
    simp only [map_mul, op_mul, hD] at h2
    exact h2
  · intro c k
    have : (op (R A) ^ k * diagOp (b ∘ e.symm) c) = op (R (A ^ k * Matrix.diagonal fun j => c (b j))) := by
      rw [map_mul, map_pow, hD, op_mul, op_pow]
      rfl
    rw [this, trace_op]
    simp only [R, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.trace, Matrix.diag,
      Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm fun j => (A ^ k * Matrix.diagonal fun j => c (b j)) j j
  · intro i₀ v hv hA hs
    refine ⟨WithLp.toLp 2 (v ∘ e.symm), ?_, ?_, ?_⟩
    · intro h
      apply hv
      funext j
      have h1 := congrArg (fun x : EuclideanSpace ℂ (Fin (Fintype.card J)) => x.ofLp (e j)) h
      simpa using h1
    · rw [op_apply]
      congr 1
      have h1 : R A = A.submatrix e.symm e.symm := by
        simp [R, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
      simp only [h1]
      rw [Matrix.submatrix_mulVec_equiv]
      have h2 : (v ∘ e.symm) ∘ e.symm.symm = v := by
        funext j
        simp
      rw [h2, hA]
    · intro c
      rw [diagOp_eq, op_apply]
      congr 1
      funext j
      simp only [Matrix.mulVec_diagonal, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h0 : v (e.symm j) = 0
      · simp [h0]
      · rw [hs _ h0]
        rfl

theorem diagonal_sigma {ι : Type} [DecidableEq ι] {κ : ι → Type} [∀ i, DecidableEq (κ i)]
    (c : ι → ℂ) : (Matrix.diagonal fun j : (Σ i, κ i) => c j.1) =
      Matrix.blockDiagonal' fun i => c i • (1 : Matrix (κ i) (κ i) ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h
    by_cases h2 : a = b
    · subst h2
      simp [Matrix.blockDiagonal'_apply]
    · simp [Matrix.blockDiagonal'_apply, Matrix.diagonal_apply, h2, Matrix.one_apply]
  · simp [Matrix.blockDiagonal'_apply, Matrix.diagonal_apply, h]

theorem blockDiagonal_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {κ : ι → Type}
    [∀ i, Fintype (κ i)] (T : ∀ i, Matrix (κ i) (κ i) ℂ) (v : (Σ i, κ i) → ℂ) (i : ι) (α : κ i) :
    (Matrix.blockDiagonal' T *ᵥ v) ⟨i, α⟩ = (T i *ᵥ fun β => v ⟨i, β⟩) α := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.blockDiagonal'_apply]
  · intro j _ hj
    simp [Matrix.blockDiagonal'_apply, hj.symm]
  · simp

theorem uModel : UModel := by
  classical
  intro ι B _ _ X _ _ _ L
  let bs : ∀ i w, Module.Basis (Fin (Module.finrank ℂ (X i w))) ℂ (X i w) :=
    fun i w => Module.finBasis ℂ (X i w)
  let M : ∀ i w, Matrix (Fin (Module.finrank ℂ (X i w))) (Fin (Module.finrank ℂ (X i w))) ℂ :=
    fun i w => LinearMap.toMatrix (bs i w) (bs i w) (L i w)
  let T : ∀ i, Matrix (∀ w, Fin (Module.finrank ℂ (X i w))) (∀ w, Fin (Module.finrank ℂ (X i w))) ℂ :=
    fun i => kron (M i)
  let A := Matrix.blockDiagonal' T
  have hc : ∀ c : ι → ℂ, Commute A
      (Matrix.diagonal fun j : (Σ i, ∀ w, Fin (Module.finrank ℂ (X i w))) => c j.1) := by
    intro c
    rw [diagonal_sigma]
    show A * _ = _ * A
    simp only [A]
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    simp
  obtain ⟨d, blk, u, h1, h2, h3⟩ := transfer (fun j : (Σ i, ∀ w, Fin (Module.finrank ℂ (X i w))) => j.1) A hc
  refine ⟨d, blk, u, h1, fun c k => ?_, fun i₀ h => ?_⟩
  · rw [h2, diagonal_sigma]
    simp only [A]
    rw [← Matrix.blockDiagonal'_pow, ← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
    refine Finset.sum_congr rfl fun i _ => ?_
    have hT : ∀ w, LinearMap.trace ℂ _ (L i w ^ k) = (M i w ^ k).trace := by
      intro w
      rw [LinearMap.trace_eq_matrix_trace ℂ (bs i w), ← LinearMap.toMatrix_pow]
    simp only [Pi.pow_apply, Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul, hT, T, kron_pow, trace_kron]
  · have hy : ∀ i w, ∃ y : X i w, i = i₀ → (y ≠ 0 ∧ L i w y = y) := by
      intro i w
      by_cases hi : i = i₀
      · subst hi
        obtain ⟨y, hy⟩ := h w
        exact ⟨y, fun _ => hy⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose y hy using hy
    let a : ∀ i w, Fin (Module.finrank ℂ (X i w)) → ℂ := fun i w => (bs i w).repr (y i w)
    have hMa : ∀ w, M i₀ w *ᵥ a i₀ w = a i₀ w := by
      intro w
      simp only [M, a]
      rw [LinearMap.toMatrix_mulVec_repr, (hy i₀ w rfl).2]
    have hne : ∀ w, ∃ x, a i₀ w x ≠ 0 := by
      intro w
      by_contra hcon
      push_neg at hcon
      apply (hy i₀ w rfl).1
      apply (bs i₀ w).repr.map_eq_zero_iff.mp
      ext x
      exact hcon x
    choose x hx using hne
    let v : (Σ i, ∀ w, Fin (Module.finrank ℂ (X i w))) → ℂ :=
      fun j => if j.1 = i₀ then ∏ w, a j.1 w (j.2 w) else 0
    refine h3 i₀ v ?_ ?_ ?_
    · intro h0
      have h1 := congrFun h0 ⟨i₀, x⟩
      simp only [v, if_true, Pi.zero_apply] at h1
      exact (Finset.prod_ne_zero_iff.mpr fun w _ => hx w) h1
    · funext ⟨i, α⟩
      simp only [A]
      rw [blockDiagonal_mulVec]
      by_cases hi : i = i₀
      · subst hi
        have hv : (fun β => v ⟨i, β⟩) = fun β => ∏ w, a i w (β w) := by
          funext β
          simp [v]
        rw [hv]
        simp only [T]
        rw [kron_mulVec]
        simp [v, hMa]
      · have hv : (fun β => v ⟨i, β⟩) = 0 := by
          funext β
          simp [v, hi]
        rw [hv]
        simp [v, hi]
    · intro j hj
      by_contra hb
      exact hj (by simp [v, hb])

end GlobalTheory.CompanionTheory.UMod
