import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalGradedLineBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFamilyPullbackProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelabelRootPowerSumAndSignsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelabelFibrePointVandermondeProduct

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
open GlobalTheory.BcEigen

namespace GlobalTheory.BcEigen

theorem bcFlag_eq_chern : Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => ∀ R : ℝ, 2 ≤ R → O.Y.arDeg ∅ R ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.Y.N)) * (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) * (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) = O.Y.chern (invForm O.Y.j (fun _ => -(((O.Y.j : ℝ) - 1) / O.Y.j)) (fun _ => -(((O.Y.N : ℝ) - O.Y.j - 1) / ((O.Y.N : ℝ) - O.Y.j))) * curveCl D.what₂.Tau O.Y.N O.Y.j) := by
  intro h2 hH hR D O hc hf A T H hr R hR2
  obtain ⟨M, Φ, Ψ, κ, hΦ, hΨ, hread⟩ := GlobalTheory.T.arithmetic_functional_graded_line_bundles h2 hH hR D O hc hf A T H hr R hR2
  rw [(hread _).1, (hread _).2]
  have hj : O.Y.j ≤ O.Y.N := O.Y.j_lt.le
  obtain ⟨e1, e2, e3⟩ := GlobalTheory.T.relabel_root_power_sum_and_signs D.what₂.Tau O.Y.N O.Y.j hj
  obtain ⟨e4, e5⟩ := GlobalTheory.T.relabel_fibre_point_vandermonde_product D.what₂.Tau O.Y.N O.Y.j hj
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  haveI := (M c).int
  haveI := (M c).V.int
  simp only [curveCl, map_mul, map_sub, map_pow, e1, e2, e3, e4, e5]
  rw [← mul_assoc]
  refine (GlobalTheory.T.flag_bundle_family_pullback_product h2 hH hR _ (M c).B (M c).V.X (M c).q (M c).V.p _ _ (M c).ar (M c).V.ar (M c).π (M c).w _ (M c).E
    (rkB D.what₂.Tau O.Y.N O.Y.j) (M c).h (M c).H (M c).fl (M c).univ (Φ c) (Ψ c) (hΦ c) (hΨ c) lamSign _).trans ?_
  rw [Finset.sum_mul]
  refine Eq.trans ?_ (map_sum (Ψ c) _ _).symm
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ∀ (g : ℝ) (x y z : MvPolynomial (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.Y.N O.Y.j a)) ℝ),
    C g * x * (y * z) = g • (x * y * z) from fun g x y z => by rw [smul_eq_C_mul]; ring]
  refine Eq.trans ?_ ((Ψ c).map_smul _ _).symm
  rw [smul_eq_mul, ← neg_mul]
  congr 1
  rcases a with ⟨τ, _ | _⟩
  · simp only [cond_false, rkB]
    rw [Nat.cast_sub hj]
  · simp [rkB]

end GlobalTheory.BcEigen

end
