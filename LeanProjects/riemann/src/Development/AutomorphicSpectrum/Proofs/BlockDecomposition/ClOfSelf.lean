import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def clOf (a : IrrGL k) (d : ℕ) : IrrCl (GL (Fin d) k) :=
  if h : a.1 = d then h ▸ a.2 else (IrrRep.det (Fin d) 1 isSmoothChar_one).cl

theorem clOf_self (a : IrrGL k) : clOf a a.1 = a.2 := by
  simp [clOf]

end GlobalTheory.CompanionTheory.WordProd

end
