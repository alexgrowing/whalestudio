import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeDifferentialsAlgebraic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_differentials_algebraic : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ), IsCMType φ →
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (N : I → Module.End Qb (HdR X₀.A))
      (m : GrpMor (dp0 Qb) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap Qb ℂ) (spMap (algebraMap Qb ℂ)) p)
      (ψ : LinearMap.BilinForm ℂ (HdR X.A)) (yv : I → HdR X.A) (w : I → ℂ),
      IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ ∧ admitted X₀ N ∧
      ∀ i, U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) ∧
        ∀ x₀ x, m.Corr x₀ x → m.Corr (N i x₀) ((ψ.flip (yv i)).smulRight (yv i) x) := by
  first | exact @GlobalTheory.CMEigen.eigen_ops | exact GlobalTheory.CMEigen.eigen_ops | (intros; apply GlobalTheory.CMEigen.eigen_ops <;> assumption)
