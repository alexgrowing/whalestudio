import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)

def JetRescale : Prop :=
  ∀ (K ι : Type) [Field K] [Finite ι] (ϖ : K) (d : ℕ) (P : MvPolynomial ι K)
    (Th : MvPowerSeries ι K), P.IsHomogeneous d →
    jetPair P (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      ϖ ^ d * jetPair P Th

def EntryDegree : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 C : ℕ) [NeZero ν] (ξ : ZMod (2 * ν) → Fin r0 → K)
    (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    (entryOp ξ e l sf T I).IsHomogeneous (∑ s, (alN e s + lsN l sf s))

def EntryChain : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 C : ℕ) [NeZero ν] (F : MvPowerSeries (ZV ν r0 r1) K)
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    (∀ x : TpV ν r1, x.1 ∉ TT → e x = 0) →
    jetPair (entryOp ξ e l sf T I) F =
      jetPair (topMonoP (Finsupp.equivFunOnFinite.symm e) * lowPoly (lowOp l sf T I))
        (MvPowerSeries.subst (zSub TT ξ) F)

end Formalism.InvariantFactorPaths.G7
