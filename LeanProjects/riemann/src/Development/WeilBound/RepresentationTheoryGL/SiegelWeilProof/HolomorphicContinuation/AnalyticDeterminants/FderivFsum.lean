import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerColumnSum

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem fsum_line (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsum t c (y + s • Matrix.single k0 0 1) =
      fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hp : piF (y + s • Matrix.single k0 0 1) = piF y := by
    ext k l
    simp [piF, Matrix.single_apply, Fin.succ_ne_zero]
    intro _ h
    exact absurd h.symm (Fin.succ_ne_zero l)
  simp only [fsum, hp]
  (simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']) <;> ring

theorem fderiv_fsum (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (hy : (1 + piF y).det ≠ 0) :
    fderiv ℂ (fsum t c) y (Matrix.single k0 0 1) = -fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hd : DifferentiableAt ℂ (fsum t c) y := (analyticAt_fsum t c y hy).differentiableAt
  have hl : HasDerivAt (fun s : ℂ => y + s • Matrix.single k0 0 (1 : ℂ)) (Matrix.single k0 0 1) 0 := by
    have h0 := ((hasDerivAt_id (0 : ℂ)).smul_const (Matrix.single k0 0 (1 : ℂ))).const_add y
    simp only [id_eq, one_smul] at h0
    exact h0
  have h1 : HasDerivAt (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1))
      (fderiv ℂ (fsum t c) y (Matrix.single k0 0 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hd.hasFDerivAt hl (by simp)
  have h2 : HasDerivAt (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1))
      (-fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1)) 0 := by
    have he : (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1)) =
        fun s => fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) :=
      funext fun s => fsum_line t c k0 y s
    rw [he]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const
      (fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1))).const_sub (fsum t c y)
  exact h1.unique h2

end PositivityTheory.Rg.Sw.LVs.CK
