import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_brk_Phi {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) (qa_P ℤ I) := by
  rw [qa_brk_eq, qa_PhiZ_apply]

theorem qa_SMu_eq {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    SMu mu = (dualWeyl ℤ n n (qa_nu mu)).map
      (qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) := by
  rw [dualWeyl_eq_span_tableauBideterminant ℤ hmu, Submodule.map_span, ← Set.range_comp]
  unfold SMu
  congr 2
  funext I
  exact qa_brk_Phi mu I

theorem standard_basis_theorem : SBasis := by
  intro n _ mu hmu
  have he : (fun I : {I : TIdx mu // StdT I} => brk mu I.1) =
      (qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) ∘
        fun I : {I : TIdx mu // StdT I} => qa_P ℤ I.1 := by
    funext I
    exact qa_brk_Phi mu I.1
  constructor
  · rw [he]
    exact (linearIndependent_standard_tableauBideterminant ℤ mu).map' (qa_PhiZ n _)
      (LinearMap.ker_eq_bot.mpr (qa_PhiZ_inj n _ (Units.isUnit _)))
  · rw [qa_SMu_eq hmu, dualWeyl_eq_span_standard_tableauBideterminant ℤ hmu, Submodule.map_span, ← Set.range_comp, he]

end Formalism.InvariantFactorPaths.ColumnFamilies
