import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf

noncomputable section

open Matrix GlobalTheory.PRep

namespace GlobalTheory.BZMir

variable (k : Type) [Field k]

def chrA (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) : Multiplicative (Fin n → k) →* ℂˣ where
  toFun v := Circle.toUnits (ψ (a ⬝ᵥ v.toAdd))
  map_one' := by simp
  map_mul' x y := by simp [dotProduct_add, AddChar.map_add_eq_mul]

def thetaA (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) : MirUin k n →* ℂˣ :=
  (chrA k ψ a).comp ((unipEquiv k n).symm.toMonoidHom.comp
    (Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)).toMonoidHom)

variable {k} [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def betaFun (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (v : V) : Mir k (n + 1) → TwJacquet τ (MirUin k (n + 1)) (mirChar k ψ n) :=
  fun g => Submodule.Quotient.mk (τ g v)

end GlobalTheory.BZMir

end
