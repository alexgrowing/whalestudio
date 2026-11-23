import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

@[reassoc (attr := simp)]
lemma toOpen_homOfLE (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) {m : ℤ} (hm : IsUnit (m : R))
    (h : W ≤ invOpen f m) : toOpen f R W hW ≫ X.homOfLE h = toInvOpen f R m hm := by
  rw [← cancel_mono (invOpen f m).ι]
  simp [Scheme.homOfLE_ι]

def SpreadHomNbhd.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ (W : X.Opens) (hWa : W ≤ invOpen f a) (hW : Set.range (baseChangeMap f ℚ) ⊆ Set.range W.ι)
      (ψ : (Scheme.Modules.pullback (X.homOfLE hWa)).obj F ⟶
        (Scheme.Modules.pullback (X.homOfLE hWa)).obj G),
      pullbackHomAlong (toOpen_homOfLE f ℚ W hW
        (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa) ψ = φ

end

end GroundTheory.Heights₂.Heights.Model
