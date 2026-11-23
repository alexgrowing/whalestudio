import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealXgen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def TwistFiniteNe.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (G B : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x) (r : ℕ) (η : Fin (r + 1) → Ω),
    x ≠ 0 → IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B.mods η →
    ∃ (n : ℕ) (bk : Fin n → ℕ) (s : Fin n → Ω),
      (∀ k, s k ∈ IndefiniteRowSideFullHecke.Kleiman.secs S x
        (IndefiniteRowSideFullHecke.Kleiman.lmul S G.mods (IndefiniteRowSideFullHecke.Kleiman.lpow S B.mods (bk k)))) ∧
      ∀ b : ℕ, IndefiniteRowSideFullHecke.Kleiman.secs S x (IndefiniteRowSideFullHecke.Kleiman.lmul S G.mods (IndefiniteRowSideFullHecke.Kleiman.lpow S B.mods b)) =
        ⨆ k, Submodule.span S (Set.image2 (· * ·) (IndefiniteRowSideFullHecke.Kleiman.secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
