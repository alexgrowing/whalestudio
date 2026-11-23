import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleModelCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousCollapseQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteLengthOfIsTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernEvaluationCollapseVerticalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousPolynomialDegreePinned

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.ConsNumber

theorem capDeg_divP_eq_sum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] (Z : NModel O) (d : ℕ) (Q : PicSym Z.X) :
    Z.capDeg_vp p d (NModel.toQ (Z.divP p)) Q =
      ∑ C ∈ Finset.univ.filter (fun C : Z.Comp => (Z.comp C).relDim = d),
        (Z.comp C).toBase.fibreDeg (picSymPull (Z.compι C) Q) := by
  rw [NModel.capDeg_vp_eq_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [NModel.vResQ_toQ, NModel.divP, NModel.vRes_div]
  exact GlobalTheory.T.capDeg_divP_eq_fibreDeg' O p (Z.comp C) _

theorem consSt (h2 : GlobalTheory.CovTop.Hypotheses2) (hH : GlobalTheory.CovHt.HypothesesH) : ConsSt := by
  intro D O hC p _ hp2 hU hlev W hW jc hPin z G hG
  have hcomm : Comm (mdlOf z jc) := GlobalTheory.T.admissible_model_commutes D O.A O.N O.j O.S O.κ p Fact.out W hW z jc
  have hI : ∀ y ∈ Ideal.span (Set.range (mdlOf z jc).Z.cD), (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP y = 0 := by
    intro y hy
    suffices h : ∀ a, (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP (a * y) = 0 by simpa using h 1
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨V, rfl⟩ := hx
      intro a
      rw [mul_comm, hcomm, (mdlOf z jc).Z.cD_divP, zero_mul, map_zero]
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add, hx, hy, add_zero]
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have e1 : (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP (evC (mdlOf z jc) (rootOf z jc) G) =
      (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP
        (aeval (fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))) (collapseQ D O.N G)) := by
    rw [← sub_eq_zero, ← map_sub]
    exact hI _ (GlobalTheory.T.chern_evaluation_collapse_vertical D O.A O.N O.j O.S O.κ p Fact.out W hW z jc G)
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  have e2 : ∀ Q : (mdlOf z jc).Z.Ch, (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP Q =
      ∑ C ∈ Finset.univ.filter (fun C : (nmodel z.Z).Comp => ((nmodel z.Z).comp C).relDim = dimFl D.what₂.Tau O.N),
        ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C) Q) := by
    intro Q
    exact capDeg_divP_eq_sum p (nmodel z.Z) _ Q
  have hcov : (0 : ℝ) < ((mdlOf z jc).cov : ℝ) := Nat.cast_pos.2 (mdlOf z jc).cov_pos
  rw [e1, e2, GlobalTheory.T.homogeneous_polynomial_degree_pinned h2 hH D O hC p hp2 hU hlev W hW jc hPin z _ (isHomogeneous_collapseQ D O.N hG),
    mul_div_cancel_left₀ _ hcov.ne']
  exact congrArg (⇑O.Y.chern) (toR_collapseQ D O.N G)

theorem main : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ConsSt := consSt

end GlobalTheory.ConsNumber

end
