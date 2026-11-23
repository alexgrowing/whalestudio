import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def DescendHom.Statement : Prop :=
  ∀ (T Y Z : Scheme.{0}) (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) (g : T ⟶ Y) (e : g' ≫ ι = g)
    (F G : Y.Modules)
    (φ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G),
    (∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn g G V)) →
    (∀ V : Y.Opens, V ≤ ι.opensRange → ∀ s : Γ(F, V), ∃ t : Γ(G, V),
      pullSectionOn g G V t = φ.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) →
    ∃ ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G,
      pullbackHomAlong e ψ = φ

end

end GroundTheory.Heights₂.Heights.Model
