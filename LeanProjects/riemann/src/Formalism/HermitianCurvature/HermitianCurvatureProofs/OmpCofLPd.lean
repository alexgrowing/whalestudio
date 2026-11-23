import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.TLC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem omp_adj_pd (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g => star (adjugate (Zhat k r z z' g) a b)) := by
  have e : (fun g => star (adjugate (Zhat k r z z' g) a b)) = fun g =>
      (fun _ => ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ)))) g *
        (((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ).det := by
    funext g
    rw [adjugate_fin_succ_eq_det_submatrix, star_mul', det_conjTranspose, star_pow, star_neg, star_one]
  rw [e]
  have := pd_mul (pd_const (N := 2 * r + k + 1) ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ))) 0)
    (pd_det (l := r) (fun g => ((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ) fun c d => by
      simpa [conjTranspose_apply] using zhat_star_pd k r z z' _ _)
  simpa using this

theorem omp_cofL_pd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg r (fun g => D.cofL Bs g s) := by
  unfold D.cofL
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega) (pd_mul (omp_adj_pd Bs.z Bs.z' (Fin.last r) a) (pd_const _ 0))

theorem omp_inv_pd (q s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (Hpk k r * gᴴ * Hpk k r) q s) := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  refine pd_sum _ fun u _ => pd_mono (show 1 + 0 ≤ 1 by omega) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun t _ => pd_mono (show 0 + 1 ≤ 1 by omega) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem omp_poly {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (j : Fin k) :
    U.IsPolyDeg (r + 1) (fun g => omC Bs B0 g j) := by
  unfold omC herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun i _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun q _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (omp_inv_pd q s) (omp_cofL_pd Bs s))

end Formalism.FourierDecayAlt.P.TLC
