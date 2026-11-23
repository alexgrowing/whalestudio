import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_lowerLeft_zero {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) (i j : Fin n) :
    mat g (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  have hx : (Pi.single (Fin.castAdd n j) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
    rw [upperHalf, LinearMap.mem_ker]
    funext k
    rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega) _
  have h1 := (hg (Pi.single (Fin.castAdd n j) 1)).1 hx
  rw [upperHalf, LinearMap.mem_ker] at h1
  have h2 := congrFun h1 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right, mulVec_single_one] at h2
  exact h2

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_levi_mul {D : D7} {A : HSp D} {μ : D.host.E} {κ : GA D (dblSp A) ≃* G D A.rank}
    (hκ : IsChart A μ κ) (p : GA D (dblSp A)) (hp : κ p ∈ P D A.rank) :
    leviMat finSumFinEquiv (mt (dblSp A) p) * rat A.gram⁻¹ = rat A.gram⁻¹ * blkA (mat (κ p)) := by
  ext i j
  have h := congrFun (congrFun (hκ p) (Fin.castAdd A.rank i)) (Fin.castAdd A.rank j)
  simp only [Matrix.mul_apply, Fin.sum_univ_add] at h
  simp only [Matrix.mul_apply, leviMat, blkA, toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, submatrix_apply, add_mul,
    Finset.sum_add_distrib, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp only [Tm, rat, Matrix.map_apply, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr, dblDec, stackRows,
    fromRows_apply_inl, fromRows_apply_inr, chart_lowerLeft_zero hp, mul_zero, Finset.sum_const_zero, add_zero] at h
  simp only [Matrix.add_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, rat, Matrix.map_apply]
  exact h.symm

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_aP_eq_det : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 →
      aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A μ hμ κ hκ p a ha
  have hP : κ p ∈ P D A.rank := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ p).1 p.2
  have h1 := congrArg Matrix.det (chart_levi_mul hκ p hP)
  rw [ha, Matrix.det_mul, Matrix.det_mul] at h1
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (gram_det_ne A)
  refine Units.ext ?_
  change (leviMat finSumFinEquiv (mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  exact hu.mul_left_cancel (by rw [mul_comm]; exact h1)

end GlobalTheory.StdUnn

end
