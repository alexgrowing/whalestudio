import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.FockCauchySchwarz

variable {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m)

theorem pairK_one (x y : VV ℂ w) :
    pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y = pairBK w (GlobalTheory.BranchNorm.cV w x) y := by
  have h := GlobalTheory.BranchNorm.pairK_eq w (1 : ι → GL (Fin m) ℂ) x y
  rw [map_one] at h
  exact h

theorem pairK_cs (x y : VV ℂ w) :
    ‖pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y‖ ^ 2 ≤
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
        (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  have hG : ∀ _ : ι, (1 : Matrix (Fin m) (Fin m) ℂ).PosDef := fun _ => Matrix.PosDef.one
  rw [← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (GlobalTheory.CoefModel.toHilb w hG x) (GlobalTheory.CoefModel.toHilb w hG y)
  rw [norm_inner_symm (GlobalTheory.CoefModel.toHilb w hG y), ← sq] at h
  exact h

theorem pairBK_sq_le : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  intro ι _ m w x y
  have h := pairK_cs w (GlobalTheory.BranchNorm.cV w x) y
  rw [pairK_one, pairK_one w (GlobalTheory.BranchNorm.cV w x), GlobalTheory.BranchNorm.cV_cV] at h
  rw [pairK_one w x x, pairBK_apply w (GlobalTheory.BranchNorm.cV w x), pairingBSymm_holds, ← pairBK_apply]
  exact h

end GlobalTheory.FockCauchySchwarz
