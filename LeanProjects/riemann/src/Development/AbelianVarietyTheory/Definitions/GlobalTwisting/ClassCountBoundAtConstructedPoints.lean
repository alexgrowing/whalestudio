import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.LocalRingCardinality.DataTies

noncomputable section

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

def ClassCountBoundAllPoints (𝒜 : FamClass) : Prop :=
  Closed (W1 𝒜) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def ClassCountBoundAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ClassCountBoundAllPoints 𝒜

def H_goodFT (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.BasicNotions.GoodFTAll (Fm.D x i)

def GoodFourierTransformAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_goodFT 𝒜

def H_hRanks (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu

def RankConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_hRanks 𝒜

def H_jOn (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤

def JInvariantConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_jOn 𝒜

def H_bu (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational

def BundleBoundAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_bu 𝒜

def H_rr (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull

def RiemannRochAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_rr 𝒜

def H_la (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

def LambdaConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_la 𝒜

structure All (𝒜 : FamClass) : Prop where
  hn4 : ClassCountBoundAllPoints 𝒜
  goodFT : H_goodFT 𝒜
  hRanks : H_hRanks 𝒜
  jOn : H_jOn 𝒜
  bu : H_bu 𝒜
  rr : H_rr 𝒜
  la : H_la 𝒜

theorem row_all {Bd : BdT} {Q : V4.Slot} {Lk : LkT Bd}
    (hn4 : ClassCountBoundAtConstructedPoints Q Lk) (goodFT : GoodFourierTransformAtConstructedPoints Q Lk) (hRanks : RankConditionAtConstructedPoints Q Lk) (jOn : JInvariantConditionAtConstructedPoints Q Lk) (bu : BundleBoundAtConstructedPoints Q Lk) (rr : RiemannRochAtConstructedPoints Q Lk) (la : LambdaConditionAtConstructedPoints Q Lk) :
    Row Q Lk fun 𝒜 _ => All 𝒜 :=
  Row.imp (Row.and hn4 (Row.and goodFT (Row.and hRanks (Row.and jOn (Row.and bu (Row.and rr (la)))))))
    fun _ _ _ ⟨a0, a1, a2, a3, a4, a5, a6⟩ => ⟨a0, a1, a2, a3, a4, a5, a6⟩

end GlobalTheory.Fc.R0

end
