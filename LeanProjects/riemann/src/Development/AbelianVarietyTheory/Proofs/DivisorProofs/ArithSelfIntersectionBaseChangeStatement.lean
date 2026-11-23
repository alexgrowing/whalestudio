import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_self_intersection_base_change : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k')
    (hρ : ρ ≫ spMap (algebraMap k k') = p) (M : HermLB (spMap (algebraMap k k'))),
    IsArithVar (spMap (algebraMap k k')) 0 → M.IsSelfInter 0 →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fun o : Option ι => o.elim (M.pull ρ hρ) L) D Φ → ∀ n : ι → ℤ,
        Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 0 := by
  first | exact @GlobalTheory.ProjCurveZero.projection_degree_zero | exact GlobalTheory.ProjCurveZero.projection_degree_zero | (intros; apply GlobalTheory.ProjCurveZero.projection_degree_zero <;> assumption)
