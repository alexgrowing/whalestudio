import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.AFTransport

open Formalism.BasicNotions

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def iotaFHom : X.B.I.F →+* D.host.F :=
  (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F
    (fun a => (X.ιE_F _).2 ⟨a, rfl⟩)

theorem iotaFHom_bijective : Function.Bijective (iotaFHom X) :=
  ⟨(iotaFHom X).injective, fun y => by
    obtain ⟨a, ha⟩ := (X.ιE_F y).1 y.2
    exact ⟨a, Subtype.ext ha⟩⟩

def iotaF : X.B.I.F ≃+* D.host.F := RingEquiv.ofBijective (iotaFHom X) (iotaFHom_bijective X)

theorem iotaF_coe (a : X.B.I.F) : ((iotaF X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

def trA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F →ₗ[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  TensorProduct.lift ((LinearMap.lsmul X.B.I.F (Formalism.MainNotions.S.Af X.B.I.F)).comp (Algebra.trace X.B.I.F X.B.I.E))

theorem trA_tmul (x : X.B.I.E) (c : Formalism.MainNotions.S.Af X.B.I.F) :
    trA X (x ⊗ₜ[X.B.I.F] c) = Algebra.trace X.B.I.F X.B.I.E x • c := rfl

def IsAdTransport (τ : Formalism.MainNotions.S.Af X.B.I.F ≃+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : Prop :=
  (∀ a : X.B.I.F, τ (algebraMap X.B.I.F (Formalism.MainNotions.S.Af X.B.I.F) a) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (iotaF X a)) ∧
    ∀ t ∈ Formalism.UG.intAd X.B.I.F, τ t ∈ Formalism.UG.intAd D.host.F

def AdTransportExists : Prop := ∃ τ, IsAdTransport X τ

def psiF (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : ℂ :=
  ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 t)

def PsiRat (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) : Prop :=
  ∀ x : X.B.I.E, X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) x) *
    psiF ψ (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (iotaF X (Algebra.trace X.B.I.F X.B.I.E x))) = 1

def PsiInfRat (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) : Prop :=
  ∀ x : X.B.I.E, Formalism.L2.SG.HidaSetting.psiEinf X.B.I x *
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf D.host.F ψ
      (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F) (iotaF X (Algebra.trace X.B.I.F X.B.I.E x))) = 1

def PsiAd (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ)
    (τ : Formalism.MainNotions.S.Af X.B.I.F ≃+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : Prop :=
  ∀ a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F, X.psiEf a * psiF ψ (τ (trA X a)) = 1

def FinUnram (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) : Prop :=
  ∀ t ∈ Formalism.UG.intAd D.host.F, psiF ψ t = 1

def SDecomp : Prop :=
  ∀ a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F, ∃ x : X.B.I.E, ∃ o ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E,
    a = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) x + o

end Formalism.L2.GlobalTheoryTheory.AFTransport
