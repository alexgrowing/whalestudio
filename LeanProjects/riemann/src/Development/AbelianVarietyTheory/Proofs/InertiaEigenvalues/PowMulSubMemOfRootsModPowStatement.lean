import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow : ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ), p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I → b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  first | exact @GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow | exact GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow | (intros; apply GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow <;> assumption)
