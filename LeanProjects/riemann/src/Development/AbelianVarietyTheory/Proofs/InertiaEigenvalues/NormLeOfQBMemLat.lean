import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem norm_le_of_qB_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M n : ℕ) (hM : 1 ≤ M) (z : ℚ_[l]) (hz : qB P z ∈ Lat AI M n) :
    ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  let J : ThetaL P AI := GlobalTheory.ThetaTie.thetaL T
  obtain ⟨a, ha⟩ := hz
  have hq : ∀ c : ℚ_[l], ‖J.θ (qB P c)‖ = ‖c‖ := by
    intro c
    have e : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ c
    rw [e, J.θ_Om]
    exact (PadicComplex.norm_extends _ _).trans (PadicAlgCl.norm_extends _ _)
  have h1 := FilB_anti (P := P) (a := 1) (b := (M : ℤ)) (by exact_mod_cast hM) ha
  have h0 := FilB_anti (P := P) (a := 0) (b := 1) (by norm_num) h1
  have hk := (J.θ_ker _ h0).2 h1
  have hadd := J.θ_add _ h0 _ (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  rw [sub_add_cancel, hk, zero_add] at hadd
  have e2 : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    simp only [map_mul, map_pow, map_natCast]
  rw [e2, J.θ_mul _ (qB_mem _) _ (io_mem AI a)] at hadd
  rw [← hq z, hadd, norm_mul, hq, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end GlobalTheory.ExpImage
