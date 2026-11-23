import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

def FibrePointsLE {Z X : Scheme.{0}} (f : Z ⟶ X) (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) (s : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z)),
    (∀ j, s j ≫ f = y) → ¬ Function.Injective s

def diagCompl {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f))ᶜ, (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

def diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (diagCompl f).toScheme ⟶ Z :=
  (diagCompl f).ι ≫ pullback.snd f f

end GlobalTheory.EtC.Tr
