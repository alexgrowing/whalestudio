import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeMainT

noncomputable section

namespace PI.RepsIndep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.UniformConstantsAndStatements NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepFix (D : D7) : Prop :=
  ∀ {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
    ∀ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ →
      ∃ γ₀ ∈ stabF D F0, (∀ a, γ₀ (F0.e a) = F0.e a) ∧ Formalism.HermitianLatticesTheory.gmap γ₀ Λ' = Λ

def StepCnt (D : D7) : Prop :=
  ∀ {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ →
    ∀ γ₀ ∈ stabF D F0, (∀ a, γ₀ (F0.e a) = F0.e a) →
      ∀ Z : Cnt.GramM D, cntZ D T' (Formalism.HermitianLatticesTheory.gmap γ₀ Λ) (lf D F0) Z = cntZ D T' Λ (lf D F0) Z

def Assembly : Prop :=
  ∀ D : D7, StepFix D → StepCnt D → ∀ u u' : D.what₂.Word, Formalism.MainNotions.S.MainBoundWithDegrees.NuTotIndep D u u'

end PI.RepsIndep
