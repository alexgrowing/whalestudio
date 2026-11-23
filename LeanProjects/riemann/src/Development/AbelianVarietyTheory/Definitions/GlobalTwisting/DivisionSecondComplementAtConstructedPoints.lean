import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.ClassTwoEntries

open GlobalTheory.Fc

def H_hh (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm CH => Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH

def HeightConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_hh 𝒜

def H_hInstR (𝒜 : FamClass) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∀ (x : ℝ) (_ : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank

def InstanceRankAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_hInstR 𝒜

def DivisionSecondComplementAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm

def DivisionSecondComplementAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => DivisionSecondComplementAdmissible 𝒜

structure All (𝒜 : FamClass) : Prop where
  hh : H_hh 𝒜
  hInstR : H_hInstR 𝒜
  aC2 : DivisionSecondComplementAdmissible 𝒜

theorem row_all {Bd : BdT} {Q : V4.Slot} {Lk : LkT Bd}
    (hh : HeightConditionAtConstructedPoints Q Lk) (hInstR : InstanceRankAtConstructedPoints Q Lk) (aC2 : DivisionSecondComplementAtConstructedPoints Q Lk) :
    Row Q Lk fun 𝒜 _ => All 𝒜 :=
  Row.imp (Row.and hh (Row.and hInstR aC2))
    fun _ _ _ ⟨a0, a1, a2⟩ => ⟨a0, a1, a2⟩

end GlobalTheory.Fc.ClassTwoEntries

end
