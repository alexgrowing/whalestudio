import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
import Formalism.LocalToGlobal.Columns.ToHLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

def BuiltCols (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ D = I.rec7 l Z

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev MtTrue : HLat B.LL :=
  MtildeH (Pr := B.primes X) B.wts I.Ch (GlobalTheory.Mem.FieldsLaws.fields_ok B) I.sel (I.tup I.mu0) I.Ps

variable (l : I.Laws) (u : B.Word)

def IsRowEmb (j : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt) : Prop :=
  ∀ (z : (MtTrue I).V) (p : (I.stX I.mu0).D ()),
    (j z).1 () p = MvPolynomial.map B.embLL (z.1 (toRow I.sel (I.tup I.mu0) p.1.1)).1

def IsPerTrue (j : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt)
    (e : (I.fm l u I.mu0).ptLat.V →ₗ[B.LL] Module.Dual B.LL (MtTrue I).V) : Prop :=
  ∀ x z, B.embLL (e x z) = (I.per l u I.mu0).period ((I.fm l u I.mu0).ptEmb x) (j z)

def AmbIsTrue (Z : TC.Later B (I.cols l)) (Am : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))) : Prop :=
  ∃ s : (MtTrue I).V ≃ₗ[B.LL] (show HLat B.LL from Mt (I.rec7 l Z) Am).V,
    (∀ z, s z ∈ (show HLat B.LL from Mt (I.rec7 l Z) Am).L ↔ z ∈ (MtTrue I).L) ∧
    (∀ (v : InfinitePlace B.LL) z,
      Formalism.HermitianLatticesTheory.normAt (show HLat B.LL from Mt (I.rec7 l Z) Am).b (show HLat B.LL from Mt (I.rec7 l Z) Am).X v (s z) =
        Formalism.HermitianLatticesTheory.normAt (MtTrue I).b (MtTrue I).X v z) ∧
    ∀ (w : B.Word) (j : (MtTrue I).V →ₛₗ[B.embLL] (I.per l w I.mu0).Mt), IsRowEmb I l w j → ∀ z,
      ((I.rec7 l Z).eMt w).symm (Am.jAmb (I.rec7 l Z).what₂.mu0 (s z)) = j z

end GlobalTheory.Core.Rk

end
