import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicEndomorphismCorankDeRham
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
theorem _root_.GlobalTheory.T.algebraic_endomorphism_corank_de_rham : GlobalTheory.Published.AbelianDeRham →
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
      (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (b : 𝓞 F) (β : Qb),
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) ≤ 2 →
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) →
      Module.rank Qb (HdR X₀.A ⧸ LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1))
        (LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) := by
  first | exact @GlobalTheory.DescRank.desc_of_baseChange | exact GlobalTheory.DescRank.desc_of_baseChange | (intros; apply GlobalTheory.DescRank.desc_of_baseChange <;> assumption)
