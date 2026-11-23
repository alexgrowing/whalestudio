import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalfOfPrimesIffLevelPb
import Formalism.LocalToGlobal.IndefiniteReal.FWTie

noncomputable section

namespace GlobalTheory.HalfOnRecord

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Pj.LPb Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare GlobalTheory.CoverHalf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)
open Formalism.L2.Host (PiBar)

variable {D : D7}

def designLevel (P : PiBar D.host) : Level (hostOfRecord D) :=
  IndefiniteRowSideFullHecke.HalfLevelCoefficients.levelAt D (IndefiniteRowSideFullHecke.HalfLevelCoefficients.halfOf D P.pb) ((ParAtCompare.levelPb_iff D P.pb).1 (levelPb_exists D P.pb P.pb_over))

theorem designLevel_spec (P : PiBar D.host) :
    (designLevel P).M = D.host.g 0 * D.host.g 1 ∧ (designLevel P).A = 1 := ⟨rfl, rfl⟩

theorem designLevel_Mb (P : PiBar D.host) :
    (designLevel P).Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := rfl

theorem bar_eq (H : ModHost D) : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
  RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowAt (R : RealDat D A Ks) (t : T0) {H : ModHost D} (l : Level H) : Prop :=
  ∃ (n : ℕ) (l₂ : Level H), IsCoverHalf l (R.Q t) n (coverHalf D (R.Q t)) l₂ ∧
    HalfIs R t l.Mb (coverHalf D (R.Q t)) ∧ AAPrimeToLevel l₂

end Rec

end GlobalTheory.HalfOnRecord
