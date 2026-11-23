import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev cED (D : D7) : AE D ≃L[AF D.host.F] (Fin (PHeisFC.nE D) → AF D.host.F) := PHeisFC.cE D.host.F D.host.E

def eInf (D : D7) : AF D.host.F := pairA D.host.F 1 0

def eFin (D : D7) : AF D.host.F := pairA D.host.F 0 1

def cEf (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) ≃ₗ[Af D.host.F] (Fin (PHeisFC.nE D) → Af D.host.F) :=
  (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun

def cEi (D : D7) : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₗ[Ainf D.host.F] (Fin (PHeisFC.nE D) → Ainf D.host.F) :=
  (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun

theorem cEf_finPart (x : AE D) : cEf D (finPart D x) = fun a => (cED D x a).2 := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp <;> rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]; funext a; simp <;> rfl
  | tmul a e =>
    funext i
    simp [finPart, cEf, cED, PHeisFC.cE, PHeisFC.bA, Algebra.TensorProduct.basis_repr_tmul]
    rfl

theorem cEi_infPart (x : AE D) : cEi D (infPart D x) = fun a => (cED D x a).1 := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp <;> rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]; funext a; simp <;> rfl
  | tmul a e =>
    funext i
    simp [infPart, cEi, cED, PHeisFC.cE, PHeisFC.bA, Algebra.TensorProduct.basis_repr_tmul]
    rfl

theorem finPart_eq_zero_iff (x : AE D) : finPart D x = 0 ↔ ∀ a, (cED D x a).2 = 0 := by
  rw [← (cEf D).map_eq_zero_iff (x := finPart D x), cEf_finPart]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

theorem infPart_eq_zero_iff (x : AE D) : infPart D x = 0 ↔ ∀ a, (cED D x a).1 = 0 := by
  rw [← (cEi D).map_eq_zero_iff (x := infPart D x), cEi_infPart]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

theorem finPart_eq_zero_iff_smul (x : AE D) : finPart D x = 0 ↔ eInf D • x = x := by
  rw [finPart_eq_zero_iff, ← (cED D).injective.eq_iff, map_smul]
  constructor
  · intro h
    funext a
    show eInf D * cED D x a = cED D x a
    exact Prod.ext (show 1 * (cED D x a).1 = (cED D x a).1 from one_mul _)
      (show 0 * (cED D x a).2 = (cED D x a).2 by rw [h a, zero_mul])
  · intro h a
    have h2 : 0 * (cED D x a).2 = (cED D x a).2 := congrArg Prod.snd (congrFun h a)
    rw [zero_mul] at h2
    exact h2.symm

theorem infPart_eq_zero_iff_smul (x : AE D) : infPart D x = 0 ↔ eFin D • x = x := by
  rw [infPart_eq_zero_iff, ← (cED D).injective.eq_iff, map_smul]
  constructor
  · intro h
    funext a
    show eFin D * cED D x a = cED D x a
    exact Prod.ext (show 0 * (cED D x a).1 = (cED D x a).1 by rw [h a, zero_mul])
      (show 1 * (cED D x a).2 = (cED D x a).2 from one_mul _)
  · intro h a
    have h2 : 0 * (cED D x a).1 = (cED D x a).1 := congrArg Prod.fst (congrFun h a)
    rw [zero_mul] at h2
    exact h2.symm

end Formalism.IndefR.Eqv

end
