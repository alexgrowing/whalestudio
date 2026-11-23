import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.BaseVacuum

theorem sum_posE {M : Type} [AddCommMonoid M] (n n' : ℕ) (f : Fin (n' * 2) → Fin (n * 2) → M) :
    ∑ i, ∑ j, f i j = ∑ p : (Fin n' × Fin n) × Fin 4, f (posE n n' p).1 (posE n n' p).2 := by
  rw [← Fintype.sum_prod_type']
  exact ((posE n n').sum_comp (fun x => f x.1 x.2)).symm

theorem putB_posE (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E)
    (p : (Fin n' × Fin n) × Fin 4) :
    putB D k x (posE n n' p).1 (posE n n' p).2 = if p.1 = k then x p.2 else 0 := by
  simp [putB]

theorem hYY_putB (D : D7) {n n' : ℕ} (k k' : Fin n' × Fin n) (x y : Fin 4 → D.host.E) :
    TaylorLogMetric.hYY D (putB D k x) (putB D k' y) =
      if k = k' then Algebra.trace D.host.K D.host.E (∑ a, x a * D.host.conj (y a)) else 0 := by
  unfold TaylorLogMetric.hYY
  rw [sum_posE]
  simp only [putB_posE]
  rw [Fintype.sum_prod_type]
  split_ifs with h
  · subst h
    rw [Fintype.sum_eq_single k]
    · simp
    · intro k'' hk
      simp [hk]
  · rw [Finset.sum_eq_zero, map_zero]
    intro k'' _
    apply Finset.sum_eq_zero
    intro a _
    by_cases h1 : k'' = k
    · subst h1
      simp [Ne.symm h, h]
    · simp [h1]

end GlobalTheory.BaseVacuum

namespace GlobalTheory.BaseVacuum

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem gamma_g_xv (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : B.γ₀.g (xv B w) = Pi.single w 1 := by
  simp [xv]

theorem trace_xv (B : Base D cc δ) (w w' : Fin 4 × D.what₂.Tau) :
    Algebra.trace D.host.K D.host.E (∑ a, xv B w a * D.host.conj (xv B w' a)) = if w = w' then 1 else 0 := by
  apply (algebraMap D.host.K D.host.E).injective
  have h := B.γ₀.isom (xv B w) (xv B w')
  rw [gamma_g_xv, gamma_g_xv] at h
  rw [map_sum, ← h]
  simp only [Pi.single_apply]
  by_cases hw : w = w'
  · subst hw
    simp
  · rw [if_neg hw, map_zero]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : u = w
    · subst hu
      simp [hw]
    · simp [hu]

theorem orthonormal_bas (B : Base D cc δ) (n n' : ℕ) : TaylorLogMetric.Orthonormal D (bas B n n') := by
  intro i j
  unfold bas
  rw [hYY_putB]
  by_cases hk : (ixE D n n' i).1 = (ixE D n n' j).1
  · rw [if_pos hk, map_sum]
    have := trace_xv B (ixE D n n' i).2 (ixE D n n' j).2
    rw [map_sum] at this
    rw [this]
    congr 1
    apply propext
    constructor
    · intro h
      exact (ixE D n n').injective (Prod.ext hk h)
    · intro h
      rw [h]
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (by rw [h])

set_option synthInstance.maxHeartbeats 200000 in

theorem sum_g_smul_xv (B : Base D cc δ) (y : Fin 4 → D.host.E) :
    ∑ w, B.γ₀.g y w • xv B w = y := by
  have h1 : ∑ w, B.γ₀.g y w • (Pi.single w (1 : D.host.K) : Fin 4 × D.what₂.Tau → D.host.K) = B.γ₀.g y := by
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  calc ∑ w, B.γ₀.g y w • xv B w = B.γ₀.g.symm (∑ w, B.γ₀.g y w • Pi.single w (1 : D.host.K)) := by
        simp only [map_sum, map_smul, xv]
    _ = y := by rw [h1, LinearEquiv.symm_apply_apply]

theorem matrix_eq_sum_putB (B : Base D cc δ) (n n' : ℕ) (M : Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E) :
    M = ∑ k : Fin n' × Fin n, ∑ w : Fin 4 × D.what₂.Tau,
      B.γ₀.g (fun a => M (posE n n' (k, a)).1 (posE n n' (k, a)).2) w • putB D k (xv B w) := by
  ext i j
  obtain ⟨p, hp⟩ := (posE n n').surjective (i, j)
  have hi : i = (posE n n' p).1 := by rw [hp]
  have hj : j = (posE n n' p).2 := by rw [hp]
  subst hi hj
  simp only [Matrix.sum_apply, Matrix.smul_apply, putB_posE, smul_ite, smul_zero]
  rw [Fintype.sum_eq_single p.1]
  · simp only [if_true]
    have := congrFun (sum_g_smul_xv B (fun a => M (posE n n' (p.1, a)).1 (posE n n' (p.1, a)).2)) p.2
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply] at this
    rw [this]
  · intro k hk
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg (Ne.symm hk)]

theorem onB_bas : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.OnB D (bas B n n') := by
  intro D cc δ B n n'
  refine ⟨orthonormal_bas B n n', ?_⟩
  refine eq_top_iff.2 fun M _ => ?_
  rw [matrix_eq_sum_putB B n n' M]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨(ixE D n n').symm (k, w), ?_⟩
  simp [bas]

end GlobalTheory.BaseVacuum
