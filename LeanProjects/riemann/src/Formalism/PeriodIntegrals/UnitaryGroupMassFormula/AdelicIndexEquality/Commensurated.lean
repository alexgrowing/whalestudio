import Formalism.PeriodIntegrals.AdIndexEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

section General

variable {G : Type} [Group G]

def dIdx (K : Subgroup G) (x : G) : ℕ := (K.map (MulAut.conj x).toMonoidHom).relIndex K

def modQ (K : Subgroup G) (x : G) : ℚ := (dIdx K x : ℚ) / (dIdx K x⁻¹ : ℚ)

def Commensurated (K : Subgroup G) : Prop := ∀ x : G, dIdx K x ≠ 0

end General

def KComm : Prop := ∀ I : AutInst, Commensurated (PI.AdIndexEq.Ksub I)

def matV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    GL (Fin I.n) (I.E ⊗[I.F] Af I.F) →* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :=
  Formalism.UG.bc (PI.FinKW.psiV I v).toRingHom

def SuppAt (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : I.Gf) : Prop :=
  ∀ w, w ≠ v → matV I w (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = 1

def IsFieldAt (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Prop :=
  IsField (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)

def ReduceLoc : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    x ∈ Subgroup.closure ({y | ∃ v, SuppAt I v y} ∪ (PI.AdIndexEq.Ksub I : Set I.Gf))

def LocSplit : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), ¬ IsFieldAt I v →
    ∀ y : I.Gf, SuppAt I v y → modQ (PI.AdIndexEq.Ksub I) y = 1

def LocInert : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ y : I.Gf, SuppAt I v y → modQ (PI.AdIndexEq.Ksub I) y = 1

def sigV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  (Algebra.TensorProduct.map (AlgHom.id I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)) I.cm.sig).toRingHom

def inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    I.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  Algebra.TensorProduct.includeRight.toRingHom

def Uv (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Subgroup (GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :=
  Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))

def Kv (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Subgroup (GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :=
  Formalism.L2.SG.Sub.Kloc (E := I.E) v (I.L : Set (Fin I.n → I.E))

def MatVU : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : I.Gf),
    matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Uv I v

def LiftU : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)),
    g ∈ Uv I v → ∃ y : I.Gf, matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g ∧ SuppAt I v y

def KLocGlob : Prop :=
  ∀ (I : AutInst) (y : I.Gf),
    y ∈ PI.AdIndexEq.Ksub I ↔ ∀ v, matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Kv I v

def MatVInj : Prop :=
  ∀ (I : AutInst) (y z : I.Gf),
    (∀ v, matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = matV I v (z : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) → y = z

def LocInertChi : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ χ : Uv I v →* ℚ, (∀ g, 0 < χ g) →
      (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → χ s = 1) →
      (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧ (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) → χ s = 1) →
      ∀ g, χ g = 1

def LocSplitChi : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), ¬ IsFieldAt I v →
    ∀ χ : Uv I v →* ℚ, (∀ g, 0 < χ g) →
      (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → χ s = 1) →
      (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧ (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) → χ s = 1) →
      ∀ g, χ g = 1

end PI.UnitaryGroupMassFormula.AdIndexEq

end
