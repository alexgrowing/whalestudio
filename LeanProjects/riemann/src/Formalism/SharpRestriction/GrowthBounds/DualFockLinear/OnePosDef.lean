import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OpBound
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd)
open Formalism.L2.G.Model.TS (fockR)

def word1 {K : Type} [CommRing K] {k : ℕ} (l : List (Fin k × Fin k)) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  l.foldr (fun y f => X y.1 * pderiv y.2 f) f

def OnePos : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d c : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν 0 ≤ c →
    ∀ β ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ s ∈ dualWeyl K (m + 1) (m + 1) ν,
      ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1)))) (a : List (Fin (m + 1) × Fin (m + 1)) → K),
        (∀ l ∈ L, l.length ≤ c) ∧
        ∀ P ∈ Hd K (m + 1) d, ∀ Q ∈ Hd K (m + 1) d,
          fockR (theta K m vec P * s) (theta K m vec Q * β) =
            fockR (theta K m vec (∑ l ∈ L, a l • word1 l P)) (theta K m vec Q)

end Formalism.MainNotions.TestSideCounting
