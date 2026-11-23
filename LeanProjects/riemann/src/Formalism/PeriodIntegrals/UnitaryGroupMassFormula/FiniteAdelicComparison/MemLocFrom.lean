import Mathlib
import Formalism.PeriodIntegrals.AdBridgeSteps

noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

def psiV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F →ₐ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E)).comp
    (Algebra.TensorProduct.comm I.F I.E (Formalism.MainNotions.S.Af I.F)).toAlgHom

def vecV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  fun i => psiV I v (x i)

def MemLocTo : Prop :=
  ∀ (I : AutInst) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), x ∈ I.Lf →
    ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))

def MemLocFrom : Prop :=
  ∀ (I : AutInst) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F),
    (∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) → x ∈ I.Lf

def InjV : Prop :=
  ∀ (I : AutInst) (z : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), (∀ v, psiV I v z = 0) → z = 0

def LiftV : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    ∃ x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, vecV I v x = y ∧ ∀ w, w ≠ v → vecV I w x = 0

end PI.FinKW
