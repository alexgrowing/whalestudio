import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamEigenspaceCorankLeTwo
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_de_rham_eigenspace_corank_le_two : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X), IsCMType φ →
    ∀ (i : I) (b₀ : 𝓞 (FR E)), (∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i) →
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) := by
  first | exact @GlobalTheory.RealMultEigen.rank_coker_le_two | exact GlobalTheory.RealMultEigen.rank_coker_le_two | (intros; apply GlobalTheory.RealMultEigen.rank_coker_le_two <;> assumption)
