import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

def SpreadsOn (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    (W : X.Opens) : Prop :=
  ∃ E' : (W : Scheme.{0}).Modules, IsVectorBundle E' ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E)

def SpreadLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (E : (baseChange f (ZLoc p)).Modules),
    IsVectorBundle E → ∀ x : baseChange f (ZLoc p),
      ∃ W : X.Opens, x ∈ baseChangeMap f (ZLoc p) ⁻¹ᵁ W ∧ SpreadsOn f (ZLoc p) E W

def specZLocToBaseChange :
    Spec (CommRingCat.of (ZLoc ⟨2, Nat.prime_two⟩)) ⟶ baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (Int.castRingHom _))) (𝟙 _) (by simp)

end

end GroundTheory.Heights₂.Heights.Model
