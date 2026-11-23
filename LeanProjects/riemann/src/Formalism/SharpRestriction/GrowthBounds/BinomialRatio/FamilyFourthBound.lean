import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Transported

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def FamilyFifthBound (D : Formalism.BasicNotions.D7) : Prop := ∀ C0 CE1 CE2, PointsLemma D C0 CE1 CE2

def RestFree (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => FreeTopRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RemainderSegmentBoundFirst (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ExtendedDichotomy D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def FamilyFourthBound (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∀ Ckap : ℝ, 0 < Ckap → ∃ Cs : ℝ, 0 < Cs ∧
    ExtendedKappaBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs

def RemainderSegmentBoundThird (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    ExtendedOrderBound D C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc

def RootMultiplicityTwoBeyond (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RootMultiplicityTwo D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RemainderSegmentBoundSecond (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ∃ Ck0 : ℝ, 0 < Ck0 ∧ ∀ Ckap : ℝ, Ck0 ≤ Ckap →
    ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc

def RestExt (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ck0 Ct0 : ℝ, 0 < Ck0 ∧ 0 < Ct0 ∧ ∀ Ckap Ct : ℝ, Ck0 ≤ Ckap → Ct0 ≤ Ct →
    HerrExtensionClass D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc

theorem closed_of_rests {D : Formalism.BasicNotions.D7} (h3 : FamilyFifthBound D) (hF : RestFree D) (hA1 : RemainderSegmentBoundFirst D) (h2 : FamilyFourthBound D)
    (hA3 : RemainderSegmentBoundThird D) (hR : RootMultiplicityTwoBeyond D) (hA2 : RemainderSegmentBoundSecond D) (hE : RestExt D) : Closed (ExtendedAllConclusions D) := by
  apply closed_of_thr
  refine TransportedAlt.mono ?_ ((((((hF.and hA1).and h2).and hA3).and hR).and hA2).and hE)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨⟨⟨⟨f, a1⟩, k2⟩, ⟨Ct0, hCt0, a3⟩⟩, r2⟩, ⟨Ck0, hCk0, a2⟩⟩,
    ⟨Ck1, Ct1, hCk1, hCt1, e⟩⟩
  obtain ⟨Cs, hCs, k2⟩ := k2 (max Ck0 Ck1) (lt_max_of_lt_left hCk0)
  refine ⟨max Ck0 Ck1, max Ct0 Ct1, Cs, lt_max_of_lt_left hCk0, lt_max_of_lt_left hCt0, hCs, ?_⟩
  exact ⟨e _ _ (le_max_right _ _) (le_max_right _ _), k2, h3 _ _ _, r2.toExtendedDigitRankBound.toDigitRankBound, a1, a2 _ (le_max_left _ _),
    a3 _ (le_max_left _ _), r2.toExtendedDigitRankBound, r2, f⟩

end Formalism.MainNotions.ColumnSystems.Pf
