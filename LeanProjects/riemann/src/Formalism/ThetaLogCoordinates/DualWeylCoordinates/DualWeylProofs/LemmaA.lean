import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem claimA_straightening : LemmaA := by
  intro n _ mu _ F _
  have hu : IsUnit (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) :=
    (Units.isUnit _).map _
  have h := (linearIndependent_standard_tableauBideterminant F mu).map' (qa_Phi F n _) (LinearMap.ker_eq_bot.mpr (qa_Phi_inj F n _ hu))
  have he : (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1)) =
      (qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n))) ∘
        fun I : {I : TIdx mu // StdT I} => qa_P F I.1 := by
    funext I
    exact qa_mapCoord_brk mu F I.1
  rw [he]
  exact h

end Formalism.InvariantFactorPaths.ColumnFamilies
