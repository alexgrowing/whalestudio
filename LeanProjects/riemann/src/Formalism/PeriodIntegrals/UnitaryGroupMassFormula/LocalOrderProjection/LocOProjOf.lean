import Mathlib
import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.AlgebraMapMemO

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.OProj

def Concl {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module E W] (P : Submodule M.L.O W), P.FG →
    Module.Projective M.L.O P

def SqCase : Prop :=
  AllLoc fun {F} _ _ _ {E} _ _ _ _ M =>
  ∀ θ ∈ M.L.O, M.L.cj θ = -θ → ∀ D : 𝒪[F], (D : F) ≠ 0 → θ * θ = algebraMap F E D →
    (∃ s : F, s * s = D) → Concl M

def NonSqCase : Prop :=
  AllLoc fun {F} _ _ _ {E} _ _ _ _ M =>
  ∀ θ ∈ M.L.O, M.L.cj θ = -θ → ∀ D : 𝒪[F], (D : F) ≠ 0 → θ * θ = algebraMap F E D →
    (¬ ∃ s : F, s * s = D) → Concl M

theorem locOProj_of (hS : SqCase) (hN : NonSqCase) : PI.LocHerm.LocOProj := by
  intro F _ _ _ E _ _ _ _ M hM
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨θ, hθ, hc, D, hD0, hD⟩ := PI.LocHerm.SlopeTestRemainingChoices.exists_theta (L := M.L)
  by_cases hs : ∃ s : F, s * s = D
  · exact hS F E M hM θ hθ hc D hD0 hD hs
  · exact hN F E M hM θ hθ hc D hD0 hD hs

end PI.LocHerm.OProj
