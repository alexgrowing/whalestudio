import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StCutRestrLenExact
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubInsertion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

universe u w

section Combinatorics

end Combinatorics

section Snoc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

end Snoc

section Dim

end Dim

theorem InterNumCut.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  _root_.UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof hF hA hB

end

end GroundTheory.Heights₂.Heights.Kleiman
