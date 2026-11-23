import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowColsBF

open GlobalTheory.RowShape GlobalTheory.RowChain GlobalTheory.StairCols

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem tiltSc_odd {j : ℕ} (hj : Odd j) (p : Fin (D.R.m - 1 - j)) (hp : 2 * p.1 < D.R.m - 1 - j) :
    tiltSc D j p = (D.host.xi0 ^ p.1)⁻¹ := by
  rw [tiltSc, if_pos hj, if_pos hp]

theorem tiltSc_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p = 1 := by
  rw [tiltSc, if_neg hj]

theorem besCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (besDecAt G j σ hj).jX i a =
      fun k => (a * incA D (D.host.xi0 ^ i.1)) * incA D ((G.rowDec j (by omega)).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso, rat, Matrix.map_apply,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id_eq, map_mul]
  ring

theorem jacCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (xZero (rowJac G (j + 1) (by omega) σ (by omega))) i a =
      fun k => a * incA D ((G.rowDec (j + 1) (by omega)).a k (Fin.castLE (by omega) i)) := rfl

theorem cols (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : GlobalTheory.FinPl.Pl D) :
    GlobalTheory.FinPl.ColsAt (besDecAt G j σ hj) (xZero (rowJac G (j + 1) (by omega) σ (by omega)))
      (rowN G j) (rowN G (j + 1)) v := by
  intro i a ha
  have hjm : j < D.R.m := by omega
  have hjm' : j + 1 < D.R.m := by omega
  obtain ⟨k, hk⟩ := D.R.m_even
  have hev : ¬ Odd j := by
    rw [Nat.not_odd_iff_even]; exact ⟨k - σ - 1, by omega⟩
  have hod : Odd (j + 1) := ⟨k - σ - 1, by omega⟩
  rw [besCol_eq G j σ hj i a, jacCol_eq G j σ hj i a]
  have l1 : rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (rowId D j) := dif_pos hjm
  have l2 : rowN G (j + 1) = (G.rowDec (j + 1) hjm').lat (G.Λ (.top (j + 1))) (rowId D (j + 1)) := dif_pos hjm'
  have hpr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  have hqr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - (j + 1)) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  rw [GlobalTheory.FinPl.latV, l1, col_mem_iff (G.rowDec j hjm) _ hpr _ _ 1 {1}
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact FractionalIdeal.one_mem_one _)
    (fun x hx => by
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨1, rfl, o, (one_mul _).symm⟩) v]
  rw [GlobalTheory.FinPl.latA, l2, col_mem_iff (G.rowDec (j + 1) hjm') _ hqr _ _ D.host.AA {a | a ∈ D.host.AA} (fun x hx => hx)
    (fun x hx => ⟨x, hx, 1, by simp⟩) v]
  have e3 : D.host.AA * rowId D (j + 1) (Fin.castLE (by omega) i) =
      FractionalIdeal.spanSingleton _ (D.host.xi0 ^ i.1)⁻¹ * (1 * rowId D j (Fin.castLE (by omega) i)) := by
    rw [rowId, rowId, tiltSc_even hev, tiltSc_odd hod _ (by simp only [Fin.val_castLE]; omega),
      FractionalIdeal.spanSingleton_one, one_mul, one_mul, stairId, stairId]
    simp only [Fin.val_castLE]
    have h1 : D.R.m - 1 - j - i.1 = (D.R.m - 1 - (j + 1) - i.1) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [e3, GlobalTheory.StairLine.mem_idV_inv_mul (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), mul_comm a]

theorem colsAt_bf : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
      (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => fun j σ hj v => cols ch.G j σ hj v⟩⟩

end GlobalTheory.RowColsBF
