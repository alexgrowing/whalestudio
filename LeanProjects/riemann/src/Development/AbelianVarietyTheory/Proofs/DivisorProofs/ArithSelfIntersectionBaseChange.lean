import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLineBundleGeneratingSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleSmoothMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionEqHalfSumWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionPowScalesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSelfIntersectionTwistPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSelfIntersectionWeightFormulaStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.ProjCurveZero

theorem projection_degree_zero : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k')
    (hρ : ρ ≫ spMap (algebraMap k k') = p) (M : HermLB (spMap (algebraMap k k'))),
    IsArithVar (spMap (algebraMap k k')) 0 → M.IsSelfInter 0 →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fun o : Option ι => o.elim (M.pull ρ hρ) L) D Φ → ∀ n : ι → ℤ,
        Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 0 := by
  intro hC _hD k _ X _ p D hX k' _ _ _ ρ hρ M hk' hM ι _ L Φ hΦ n
  obtain ⟨e, he, t, ht⟩ := GlobalTheory.T.exists_pow_line_bundle_generating_section k k' hk' M.B M.isLB
  obtain ⟨c, hc, hcc, hiso⟩ := GlobalTheory.T.hermitian_line_bundle_smooth_metric k (Sp k') (spMap (algebraMap k k')) (M.pow e) t ht
  have h1 := GlobalTheory.T.self_intersection_pow_scales hC k (Sp k') (spMap (algebraMap k k')) 0 hk' M 0 hM e
  have h2 := hiso.symm.isSelfInter hk' h1
  have h3 := GlobalTheory.T.self_intersection_eq_half_sum_weights k k' hk' c hc hcc _ h2
  have hsum : ∑ᶠ σ, ∑ᶠ y, c σ y = 0 := by
    simp only [mul_zero] at h3
    linarith
  have h4 := GlobalTheory.T.arithmetic_self_intersection_weight_formula hC k X p D hX k' ρ hρ hk' c hc hcc hsum ι L n
  have h5 := GlobalTheory.T.arithmetic_self_intersection_twist_pow hC k X p D hX k' ρ hρ M e c hc hcc hiso ι L Φ hΦ n
  rw [h4, mul_zero] at h5
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  exact (mul_eq_zero.1 h5).resolve_left he'

end GlobalTheory.ProjCurveZero
