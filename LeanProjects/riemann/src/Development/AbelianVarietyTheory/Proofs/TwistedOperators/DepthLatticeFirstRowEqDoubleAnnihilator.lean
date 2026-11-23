import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShiftStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowZeroLeSelfDualHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.LatticeBidual

theorem latRow_bidual : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u → (∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ v ∈ latRow G i, W.ψ (symplO _ _ v u') = 1) → W.ψ (symplO _ _ u u') = 1) → u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM i hi u hu H
  have sdG : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.grid j 0)) (G.Λ (.grid j 0)) := by
    intro j hj
    cases j with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ j => exact (G.sp.V_is (j + 1) 0 (by omega) hj (by omega)).sd
  have sdS := sdG (i + 1) hi
  have sdT := sdG i hi.le
  have sdB : IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' sdT h1 h2
  have hO : ∀ v ∈ latRow G i, v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := fun v hv => GlobalTheory.RowLoc.mem_latO_negSp.1 hv.1
  have hB : ∀ v ∈ latRow G i, v ∈ latBig G i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · exact fun v hv => GlobalTheory.T.depthLatticeGridRow_zero_le_selfDualHomLattice D hq T L μ0 hL sc G W M hM hi hv
    · exact fun v hv => GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM i hi1 hi hv
  have hdep := GlobalTheory.T.idempotent_smul_mem_hat_lattice D hq T L μ0 hL sc G W M hM i hi
  have finO := (GlobalTheory.AscFinWit.finLat_latO sdS.1 sdT.1).fin
  have finB := (GlobalTheory.AscFinWit.finLat_latO (LS := G.Λ (.grid (i + 1) 0)) sdS.1 sdB.1).fin
  have uO : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finO u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) v (finO v (hO v hv))).1 (hO v hv) u' hu'
  have uB : u ∈ latBig G i := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finB u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) v (finB v (hB v hv))).1 (hB v hv) u' hu'
  exact ⟨GlobalTheory.RowLoc.mem_latO_negSp.2 uO, hdep u uO uB⟩

end GlobalTheory.AscFin.LatticeBidual
