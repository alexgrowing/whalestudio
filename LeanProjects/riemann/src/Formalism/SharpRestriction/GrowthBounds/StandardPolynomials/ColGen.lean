import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultidegAdd
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def colGens (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    Set (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  {x | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧
    ∃ y : Tx r (D.lettersAt j jp), y ∈ sAll (D.lettersAt j jp) D.T.J D.T.thr ∧
    ∃ γ : Fin r → ℕ, ∑ c, γ c = D.B - jp ∧
    x = (∏ i, D.Ehat O (r := r) i ^ j i) * D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      rename (chainEmb N r D.T.t) (psiR (KK O) (D.lettersAt j jp) y) * ∏ c, X (xiVar N r D.T.t c) ^ γ c}

def FacSysAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ s : Syms O C0 CE1 CE2 X,
      (∀ j, s j ∈ colGens O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) →
      Nonempty (FacSys C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β) (symFam (KK O) X.p C0 CE1 CE2 X β s))

def FacSysCondition : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
