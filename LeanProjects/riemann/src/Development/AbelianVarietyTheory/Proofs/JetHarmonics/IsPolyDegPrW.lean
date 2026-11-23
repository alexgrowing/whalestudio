import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

theorem isPolyDeg_prW {N : ℕ} (k r d : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (v : Matrix (Fin N) (Fin N) ℂ → Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, U.IsPolyDeg d (fun g => v g i))
    (i : Fin (2 * r + k + 1)) : U.IsPolyDeg d (fun g => D.prW k r z (v g) i) := by
  have hb : ∀ j : Fin (2 * r + k + 1),
      U.IsPolyDeg d (fun g => if r ≤ j.val ∧ j.val ≤ r + k then v g j else 0) := by
    intro j
    by_cases h : r ≤ j.val ∧ j.val ≤ r + k
    · simpa only [if_pos h] using hv j
    · simpa only [if_neg h] using pd_const (N := N) 0 d
  unfold D.prW
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  refine pd_sub (hb i) (pd_mono (show d + 0 + 0 ≤ d by omega)
    (pd_mul (pd_mul ?_ (pd_const _ 0)) (pd_const _ 0)))
  unfold herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun a _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun b _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) (hb b))

theorem omg_isPolyDeg : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (i : Fin (2 * r + k + 1)),
    Formalism.FourierDecayAlt.U.IsPolyDeg (r + 1) (fun g : Mx k r => GlobalTheory.WigSh.omg k r z z' g i) := by
  intro k r z z' i
  unfold omg
  refine isPolyDeg_prW k r (r + 1) z' (fun g => (Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a) (fun q => ?_) i
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (P.TLC.omp_inv_pd q s) ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega)
    (pd_mul (P.TLC.omp_adj_pd z z' (Fin.last r) a) (pd_const _ 0))

end GlobalTheory.WigSh
