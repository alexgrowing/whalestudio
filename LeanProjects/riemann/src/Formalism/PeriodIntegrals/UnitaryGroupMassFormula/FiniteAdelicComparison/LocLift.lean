import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj

noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

open Classical in

def liftOne (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
  (TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E) y).sum
    fun j c => Module.Basis.ofVectorSpace I.F I.E j ⊗ₜ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV I.F v c

open Classical in
theorem evalV_singleV_same (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV I.F v c) = c := by
  first
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV]; done)
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV, RestrictedProduct.single]; done)
  | exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 I.F) => w.adicCompletion I.F) v c

open Classical in
theorem evalV_singleV_ne (I : AutInst) {v w : HeightOneSpectrum (𝓞 I.F)} (hw : w ≠ v)
    (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV I.F v c) = 0 := by
  first
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV, hw]; done)
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV, RestrictedProduct.single, hw]; done)
  | exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 I.F) => w.adicCompletion I.F) hw c

theorem psiV_liftOne_same (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : psiV I v (liftOne I v y) = y := by
  classical
  have hy : (TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E)).symm
      (TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E) y) = y :=
    LinearEquiv.symm_apply_apply _ y
  conv_rhs => rw [← hy]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, liftOne, Finsupp.sum, Finsupp.sum,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [psiV, evalV_singleV_same]

theorem psiV_liftOne_ne (I : AutInst) {v w : HeightOneSpectrum (𝓞 I.F)} (hw : w ≠ v)
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : psiV I w (liftOne I v y) = 0 := by
  rw [liftOne, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [psiV, evalV_singleV_ne I hw]

theorem local_vector_lift : LiftV := by
  intro I v y
  refine ⟨fun i => liftOne I v (y i), ?_, ?_⟩
  · funext i
    exact psiV_liftOne_same I v (y i)
  · intro w hw
    funext i
    exact psiV_liftOne_ne I hw (y i)

end PI.FinKW
