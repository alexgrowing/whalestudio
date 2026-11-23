import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsWitness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

def PeriodLatticeCM.Statement (_S : PrimeDiscriminant K) (F : CMFamily K) : Prop :=
  ∀ s : F.k →+* ℂ, ∃ L : PeriodPair,
    F.periodLattice s = L.lattice ∧ latticeEnd L = cmRing (F.restrict s)

def IdealInvArea.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), latticeEnd L = cmRing σ →
    ∀ 𝔞 : (Ideal (𝓞 K))⁰,
      latticeArea (idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice) =
        latticeArea L.lattice / (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
