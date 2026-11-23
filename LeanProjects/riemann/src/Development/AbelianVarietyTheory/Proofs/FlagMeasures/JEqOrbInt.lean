import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

variable {k r : ℕ}

def rep (L : LocBessel k r) : BranchingSupport.Rep k r := ⟨L.Hs, L.σ⟩

def BeTK (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) : Prop :=
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def SmCW (L : LocBessel k r) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : L.Hs → V) : Prop :=
  (∀ v ∈ (rep L).sm, ∀ w ∈ (rep L).sm, l (v + w) = l v + l w) ∧ (∀ (a : ℂ), ∀ v ∈ (rep L).sm, l (a • v) = a • l v) ∧
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) L.σ l

def OneAt (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : Prop :=
  ∃ A : L.Wq →L[ℂ] L.Wp, ∀ F s, IsCoef (rep L) l l' F s → OrbInt L F g ν = s • A

theorem J_eq_orbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.J F g = OrbInt L F g (pairMeas L) := rfl

end GlobalTheory.AmpTK
