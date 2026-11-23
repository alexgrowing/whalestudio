import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def LemmaA : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu → ∀ (F : Type) [Field F],
    LinearIndependent F (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1))

def SBasis : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    LinearIndependent ℤ (fun I : {I : TIdx mu // StdT I} => brk mu I.1) ∧
    Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) = SMu mu

end Formalism.InvariantFactorPaths.ColumnFamilies
