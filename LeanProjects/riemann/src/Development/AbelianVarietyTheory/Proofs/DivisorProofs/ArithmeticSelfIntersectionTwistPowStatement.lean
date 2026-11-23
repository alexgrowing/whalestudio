import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSelfIntersectionTwistPow
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_self_intersection_twist_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k')
    (hρ : ρ ≫ spMap (algebraMap k k') = p) (M : HermLB (spMap (algebraMap k k'))) (e : ℕ)
    (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ) (hc : ∀ σ y, CxPts.CInfAt (c σ) y)
    (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))), (fnB c hc hcc).Isometric (M.pow e) →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fun o : Option ι => o.elim (M.pull ρ hρ) L) D Φ → ∀ n : ι → ℤ,
        (e : ℝ) * Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
          1 / 2 * chInt (comb L n) D (fun σ y => c σ (PtsOver.map ρ hρ _ y)) := by
  first | exact @GlobalTheory.MixPull.mix_pull_eq | exact GlobalTheory.MixPull.mix_pull_eq | (intros; apply GlobalTheory.MixPull.mix_pull_eq <;> assumption)
