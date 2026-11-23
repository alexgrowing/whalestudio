import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntersectionPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedBoundaryDivisorSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPowerEqOfIntegralPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.CompPropObj

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs

theorem interPoly_int (hM : GlobalTheory.Published.MumfordProportionality) {D : D7} (O : Setup D) (c : O.s.Comp)
    (la : D.what₂.Tau → Fin O.N → ℤ) :
    (O.var c).interPoly (fun x : DV.Rt D.what₂.Tau O.N => GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x))
      ((∑ x, C ((-la x.1 x.2 : ℤ) : ℝ) * X x) ^ (O.var c).dim) =
    (O.s.cx O.L O.B O.fl).volC c * Formalism.DegreeFormula.flagDeg D.what₂.Tau O.N (fun τ i => (la τ i : ℝ)) := by
  rw [← Fin.prod_const, GlobalTheory.ProjVar.Var.interPoly_prod_sum, GlobalTheory.T.weighted_boundary_divisor_sum]
  exact GlobalTheory.ShFam.Mumford.src hM O.s O.L O.Φ c la

theorem main : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ =>
    (∀ c, (T.F c).Prop4 (A.w c)) ∧ O.Y.vol = ∑ c, A.w c ∧ Propor O.Y := by
  intro hP _ D O _ _ A T H h
  have hM : GlobalTheory.Published.MumfordProportionality := (GlobalTheory.T.stronger_published_hypotheses_imply hP).p16
  have hw : A.w = (O.s.cx O.L O.B O.fl).volC := h.aux.w
  refine ⟨fun c => ⟨hw ▸ (O.s.cx O.L O.B O.fl).volC_pos c, fun u => ?_⟩, by rw [hw]; rfl, fun Q => by
    show O.Y.vol * Formalism.L2.Geo.degFlL D.what₂.Tau O.N Q = _
    erw [Formalism.L2.Geo.degFlL_apply]; rfl⟩
  have he : (O.var c).dim = dimY O.Y := O.dim_eq c
  rw [GlobalTheory.T.monge_ampere_intersection_polynomial hP.p16.1 (h.man c) he _ _ _ ((h.an c).th u), hw]
  have key := GlobalTheory.T.polynomial_power_eq_of_integral_points (dimY O.Y) ((O.var c).interPoly fun x : DV.Rt D.what₂.Tau O.N =>
      GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)) ((O.s.cx O.L O.B O.fl).volC c • Formalism.L2.Geo.degFlL D.what₂.Tau O.N)
    (fun a => by
      have := interPoly_int hM O c fun τ i => -a (τ, i)
      simp only [neg_neg, he] at this
      refine this.trans ?_
      have hl : linRoot (fun τ i => ((-a (τ, i) : ℤ) : ℝ)) = ∑ x, C ((a x : ℤ) : ℝ) * X x := by
        simp [linRoot, Finset.sum_neg_distrib]
      show _ * degFl _ _ (linRoot _ ^ dimFl _ _) = _ * (Formalism.L2.Geo.degFlL D.what₂.Tau O.N _)
      rw [hl]
      erw [Formalism.L2.Geo.degFlL_apply]
      rfl)
    fun x => -u x.1 x.2
  rw [key, LinearMap.smul_apply, smul_eq_mul, Formalism.L2.Geo.degFlL_apply, Formalism.DegreeFormula.flagDeg]
  congr 2
  simp [Formalism.DegreeFormula.linRoot, Finset.sum_neg_distrib]
  rfl

end GlobalTheory.CompPropObj
