import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FineCut

theorem conj_cut {R : Type} [CommRing R] {n : ℕ} (β F : GL (Fin n) R) (c : R) :
    β.1 * (c • (β⁻¹ * F * β).1 + (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) * (β⁻¹).1
      = c • F.1 + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : β.1 * (β⁻¹ * F * β).1 * (β⁻¹).1 = F.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  have h2 : β.1 * (β⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h2]

theorem finE_cut : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (g k : GA D T) (ε : AE D), Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1 = βT.1 * (toEAf D ε • (βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) * (βT⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D T βT g k ε h
  have hk : (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1
      = toEAf D ε • (Formalism.IndefR.Lev.finE T g : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) := by
    show (Formalism.L2.Theta.mt T k).map (toEAf D) = toEAf D ε • (Formalism.L2.Theta.mt T g).map (toEAf D) + (1 - toEAf D ε) • 1
    rw [h, GlobalTheory.CompStab.map_idem]
  rw [hk]
  exact (conj_cut βT (Formalism.IndefR.Lev.finE T g) (toEAf D ε)).symm

end GlobalTheory.FineCut

end
