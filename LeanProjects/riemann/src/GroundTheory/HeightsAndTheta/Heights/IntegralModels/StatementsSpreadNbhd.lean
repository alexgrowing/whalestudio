import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

def toOpen (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) : baseChange f R ⟶ (W : Scheme.{0}) :=
  IsOpenImmersion.lift W.ι (baseChangeMap f R) hW

@[reassoc (attr := simp)]
lemma toOpen_ι (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) :
    toOpen f R W hW ≫ W.ι = baseChangeMap f R :=
  IsOpenImmersion.lift_fac _ _ _

def SpreadBundleNbhd.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules), IsVectorBundle E →
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f (ZLoc p) W hW)).obj E' ≅ E)

end

end GroundTheory.Heights₂.Heights.Model
