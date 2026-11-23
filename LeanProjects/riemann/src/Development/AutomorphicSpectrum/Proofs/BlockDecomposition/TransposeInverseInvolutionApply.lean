import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaInv

theorem thetaW_val_apply {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) (i j : Fin N) :
    (thetaW A N g).1 i j = (g⁻¹).1 (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix,
    Matrix.transpose_apply, Fin.revPerm]

theorem thetaW_thetaW_ring {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N (thetaW A N g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaW_val_apply, ← map_inv, thetaW_val_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem thetaW_thetaW {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k) :
    thetaW k N (thetaW k N g) = g :=
  thetaW_thetaW_ring N g

end GlobalTheory.CompanionTheory.ThetaInv

end
