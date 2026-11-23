import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideRest
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExistsClassIsLSeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.MultiProdCompInvTranspose

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace PositivityTheory.Pf1.LocalLanglands.LDual

theorem lExists_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL k, IsL 𝔪 x.rep :=
  fun k _ _ _ _ _ => GlobalTheory.LocGL.LExist.main k hS (PositivityTheory.Exh.exists_class_isLSeg k)

theorem langlandsDataDualGL_of_clauses (hS : GlobalTheory.Published.StandardCosocleGL)
    (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (l : List (Segment k)) (x y : IrrGL k), IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
        ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep) :
    GlobalTheory.Published.LanglandsDataDualGL :=
  fun k _ _ _ _ _ => ⟨lExists_of_cosocle hS k, hD k⟩

theorem langlandsDataDualGL_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) : GlobalTheory.Published.LanglandsDataDualGL :=
  langlandsDataDualGL_of_clauses hS PositivityTheory.Pf1.LDual2.langlandsDataDualGL_dual

end PositivityTheory.Pf1.LocalLanglands.LDual
