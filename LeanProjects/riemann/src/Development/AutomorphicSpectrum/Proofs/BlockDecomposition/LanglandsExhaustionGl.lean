import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProductStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LanglandsMultiseg

theorem langlandsMultisegments_of_clauses (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (hSoc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k)
    (hSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k)
    (hFree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments := by
  intro k _ _ _ _ _
  exact ⟨GlobalTheory.T.langlands_injective_of_socle hA (hSoc k) (hSeg k),
    fun 𝔪 𝔫 x y hd h₀ h₁ hy =>
      GlobalTheory.T.langlands_sum_subquotient_product hA (hSoc k) (hSeg k)
        (hFree k) (hE k) 𝔪 𝔫 x y hd h₀ h₁ hy⟩

end GlobalTheory.CompanionTheory.LanglandsMultiseg
