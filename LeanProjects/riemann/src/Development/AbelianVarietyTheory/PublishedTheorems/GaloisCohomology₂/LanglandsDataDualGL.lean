import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LanglandsDataDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL k, IsL 𝔪 x.rep) ∧
    ∀ (l : List (Segment k)) (x y : IrrGL k), IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
      ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep

end GlobalTheory.Published

end
