import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyCartierRationalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeCombinationEqIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricChernIntegralEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernRootEvalEqFlagDegreeStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagDegTie

theorem flag_gdeg_eq_degFl : Hypotheses2 → GlobalTheory.Published.ArDegree → ∀ (ι : Type) [Fintype ι] (N : ℕ) (n : ι × Fin N → ℤ), gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) (dimFl ι N) = degFl ι N (lin (fun x => (n x : ℝ)) ^ dimFl ι N) := by
  intro hP hA ι _ N n
  obtain ⟨Y, j, gr, hpb, hdim, hpres, X0, E, E', φ, f, hX, hRef, hGr⟩ := GlobalTheory.T.flag_variety_cartier_rational_model ι N
  have h1 := GlobalTheory.T.degree_combination_eq_intersection hA.2 ι N Y j hpb gr hpres n
  rw [← hdim, h1]
  let e : GlobalTheory.GoodMetric.Root (fun _ : ι => N) ≃ ι × Fin N := Equiv.sigmaEquivProd ι (Fin N)
  have hI : ((Y.inter fun _ => ∑ x, n x • gr x : ℤ) : ℝ) =
      Y.interPoly (fun x : GlobalTheory.GoodMetric.Root (fun _ : ι => N) => gr (x.1, x.2))
        (∏ _i : Fin Y.dim, ∑ x : GlobalTheory.GoodMetric.Root (fun _ : ι => N), C ((n (e x) : ℤ) : ℝ) * X x) := by
    rw [GlobalTheory.ProjVar.Var.interPoly_prod_sum]
    congr 2
    funext _
    exact (e.sum_comp (fun x => n x • gr x)).symm
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr ι (fun _ : ι => N)
    (∏ _i : Fin Y.dim, ∑ x : GlobalTheory.GoodMetric.Root (fun _ : ι => N), C ((n (e x) : ℤ) : ℝ) * X x)
  obtain ⟨σ, H, hH, hG, hT⟩ := GlobalTheory.T.good_metric_chern_integral_eval ι (fun _ : ι => N) X0 E hX
  have hc := hP.p16.flag hRef hGr hH hG hR
  rw [hI, hT R _ hc, GlobalTheory.T.chern_root_eval_eq_flag_degree ι N _ R hR, map_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  rw [map_sum, lin]
  rw [← e.sum_comp (fun x => C ((n x : ℤ) : ℝ) * (X x : MvPolynomial (ι × Fin N) ℝ))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, rename_C, rename_X]
  rfl

end GlobalTheory.FlagDegTie
