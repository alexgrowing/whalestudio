import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open scoped Matrix

namespace Zc.Cos

def invT {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] : GL n A →* GL n A where
  toFun g := ⟨(g⁻¹).1ᵀ, g.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp only [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

def thetaW (A : Type) [CommRing A] (N : ℕ) : GL (Fin N) A →* GL (Fin N) A :=
  (Units.map (Matrix.reindexAlgEquiv A A (Fin.revPerm : Equiv.Perm (Fin N))).toAlgHom.toMonoidHom).comp invT

def GKLocal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    π.IsIrreducible → Nonempty (Representation.Equiv (π.comp invT) (contra π))

end Zc.Cos

end
