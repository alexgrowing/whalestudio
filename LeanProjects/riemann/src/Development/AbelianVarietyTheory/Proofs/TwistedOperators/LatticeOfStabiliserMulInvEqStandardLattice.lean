import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.LatStdStab
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem latAt_mul_inv_eq_stdL : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ k : FinPt G X,
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X)) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V X) k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X))) →
    GlobalTheory.SumSize.latAt S X (k * (S.N.u X)⁻¹) = stdL D _ := by
  intro D T L sc G W S X hX k hk
  have hC := GlobalTheory.MovedHomLat.colLat_fin (S.N.fr X)
  have hsp := GlobalTheory.MovedHomLat.colLat_span (S.N.fr X)

  have key : ∀ y, y ∈ Formalism.UG.CS.globLat (finG (G.V X) (k * (S.N.u X)⁻¹)) (G.Λ X) ↔ y ∈ colLat (S.N.fr X) := by
    intro y
    have e : finG (G.V X) (k * (S.N.u X)⁻¹) * Formalism.IndefR.Lev.finE (G.V X) (S.N.u X).1 =
        Formalism.IndefR.Lev.finE (G.V X) k.1 := by
      show Formalism.IndefR.Lev.finE (G.V X) ((k * (S.N.u X)⁻¹ : FinPt G X) : GA D (G.V X)) * _ = _
      rw [← map_mul]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [GlobalTheory.MovedHomLat.globLat_mul_iff _ _ _ _ (S.N.u_lat X hX), e, GlobalTheory.MovedHomLat.mem_globLat_iff]
    rw [hk, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact GlobalTheory.CongStdLoc.incl_mem_hatL_iff (F := D.host.F) (Module.Finite.iff_fg.1 hC) hsp y
  ext z
  simp only [GlobalTheory.SumSize.latAt, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [key]
  have := congrArg (z ∈ ·) (GlobalTheory.ColStd.colLat_comap_eq_stdLat (S.N.fr X))
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at this
  exact Iff.of_eq this

end GlobalTheory.LatStdStab
