import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.DualWeylModuleStable
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

noncomputable section

open MvPolynomial

namespace Formalism.UG

def dualWeylRep (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Representation R (GL (Fin r) R) (Formalism.GradedWeylDivisibility.dualWeyl R r n ν) where
  toFun g := (dwAct R r n g).toLinearMap.restrict
    (fun f hf => Formalism.UG.P.dual_weyl_module_stable R r n ν g f hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n 1 (f : MvPolynomial (Fin r × Fin n) R) = (f : MvPolynomial (Fin r × Fin n) R)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n (g * h) (f : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g (dwAct R r n h f)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n g h).1]
    rfl

def weylRepW (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Representation R (GL (Fin r) R) (Formalism.GradedWeylDivisibility.weyl R r n hn ν) where
  toFun g := (dwAct R r n g).toLinearMap.restrict
    (fun f hf => Formalism.UG.P.weyl_module_GL_stable R r n hn ν g f hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n 1 (f : MvPolynomial (Fin r × Fin n) R) = (f : MvPolynomial (Fin r × Fin n) R)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n (g * h) (f : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g (dwAct R r n h f)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n g h).1]
    rfl

theorem dualWeylRep_apply (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    ((dualWeylRep R r n ν g f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g f := rfl

end Formalism.UG
