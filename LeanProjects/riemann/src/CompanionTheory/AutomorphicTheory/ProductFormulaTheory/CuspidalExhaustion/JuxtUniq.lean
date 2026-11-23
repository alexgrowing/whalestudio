import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDefs

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isLSeg (Δ : Segment k) (x y : IrrGL k) (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, c⟩ := x
  obtain ⟨m, d⟩ := y
  have h1 : n = m := hx.deg_eq.symm.trans hy.deg_eq
  subst h1
  obtain ⟨φ⟩ := hx.unique hy
  exact congrArg (Sigma.mk n) (irrCl_eq_iff.2 ⟨φ.symm⟩)

end CompanionTheory.Exh

end
