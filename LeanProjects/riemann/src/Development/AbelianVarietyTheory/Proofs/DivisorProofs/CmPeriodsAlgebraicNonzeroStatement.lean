import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodsAlgebraicNonzero
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
theorem _root_.GlobalTheory.T.cm_periods_algebraic_nonzero : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
      (U : Unif φ L 0 X), IsCMType φ → X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (i : I) (y₀ : HdR X₀.A), y₀ ≠ 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        act (dp0 Qb) (𝟙 _) X₀.rm b y₀ = β • y₀) →
    ∀ f f' : Module.Dual Qb (HdR X₀.A), f y₀ = 0 → f' y₀ = 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        ∀ x, f (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f x ∧ f' (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f' x) →
      ∀ x y, f x * f' y = f y * f' x := by
  first | exact @GlobalTheory.EigenFunctional.mul_comm_of_eigen | exact GlobalTheory.EigenFunctional.mul_comm_of_eigen | (intros; apply GlobalTheory.EigenFunctional.mul_comm_of_eigen <;> assumption)
