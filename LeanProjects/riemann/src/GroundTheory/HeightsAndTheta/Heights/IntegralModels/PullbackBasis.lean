import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

def pullSectionOn {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) (U : Z.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U).hom

lemma pullSectionOn_top {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) :
    pullSectionOn g M ⊤ = pullSection g M := rfl

def PullbackBasis.Statement : Prop :=
  ∀ (T Z : Scheme.{u}) (g : T ⟶ Z) (M : Z.Modules) (U : Z.Opens) (n : ℕ) (s : Fin n → Γ(M, U)),
    IsBasisOn M U s →
      IsBasisOn ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (fun i => pullSectionOn g M U (s i))

end

end GroundTheory.Heights₂.Heights.Model
