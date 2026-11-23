import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShapeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPointStatement

set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
theorem GlobalTheory.RefSum.refCore_of_size_sumPt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt → _root_.GlobalTheory.RefSum.ReferenceCore := by
  intro hS hSum
  refine Closed.imp (Closed.and hSum (Closed.and (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS) (_root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo hS))) ?_
  rintro eps Fm CH - ⟨⟨C1, hC1, h1⟩, ⟨C2, -, h2⟩, C3, hC3, h3⟩
  refine ⟨C1 + C3, add_nonneg hC1 hC3, (h1.and (h2.and h3)).imp fun x0 h x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨k1, k2, k3⟩ := h x hx hle ι p hp
  obtain ⟨S, e, s, hP, hs, hO⟩ := k1 i hi u1 hu
  obtain ⟨-, -, -, -, -, -, hD, hL, -⟩ := k2 i hi u1 hu
  obtain ⟨hJ, hr, hg⟩ := k3 i hi u1 hu
  have hI : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  refine ⟨_, _, _, primeSum_add_pair hP (Fm.D x ι).host.g (Fm.D x ι).host.g_prime, by rw [mul_add, add_mul]; exact add_le_add hs hg,
    fun q hq => ?_⟩
  by_cases hq' : q ∈ Finset.univ.image (Fm.D x ι).host.g
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq'
    refine (GlobalTheory.T.supLatticeReferenceExponent_thetaWeight_level_le_one _ p.T.toCore p.fw.laws.toLawsM (Fm.ex x hx ι).errX _ hI _ _ _ hD hL sum_le_nCol hr hJ k).trans
      (EReal.coe_le_coe_iff.2 ?_)
    simp only [if_pos hq']
    linarith [hP.2.1 ((Fm.D x ι).host.g k)]
  · haveI := Fact.mk hq
    have hne : ∀ k, q ≠ (Fm.D x ι).host.g k := fun k h => hq' (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h.symm⟩)
    refine (GlobalTheory.T.baseLocusExponent_le_oscillation_nonTypePrime _ p.T.toCore p.fw.laws.toLawsM (Fm.ex x hx ι).errX _ hI _ _ _ hD hL sum_le_nCol hr hJ q hne _
      (hO q hne)).trans (EReal.coe_le_coe_iff.2 ?_)
    simp only [if_neg hq', add_zero, le_refl]
end
