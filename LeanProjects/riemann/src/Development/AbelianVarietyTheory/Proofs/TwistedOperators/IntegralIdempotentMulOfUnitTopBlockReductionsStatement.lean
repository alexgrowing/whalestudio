import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions : ∀ {D : D7} (m n : ℕ), n ≤ m → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (u : Matrix (Fin m) (Fin n) (EAf D)) (γ : GL (Fin n) (EAf D)), IsIntM u → IsIntM (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1) → (∀ i j, toEAf D e * u i j = u i j) → (∀ PP ∈ Z, IsUnit (topL n (redM PP u)).det) → (∀ PP ∈ Z, IsUnit (topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1))).det) → IsIntM (toEAf D e • γ.1) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) ∧ ∀ PP ∈ Z, topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1)) * redM PP (toEAf D e • γ.1) = topL n (redM PP u) := by
  first | exact @GlobalTheory.HalfUnit.int_of_unit_tops | exact GlobalTheory.HalfUnit.int_of_unit_tops | (intros; apply GlobalTheory.HalfUnit.int_of_unit_tops <;> assumption)
