import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFlagGradedIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFlagBottChernSumStatement
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
namespace GlobalTheory.DualFlag

theorem isFlagCh2_dual : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S] (r : ℕ) (E : HermVB p r) (fl : Vert.Flag E.E r) (a : ℝ), IsRegSurf p → VMetric.IsFlagCh2 E.cInf fl a → ∃ fl' : Vert.Flag E.dual.E r, VMetric.IsFlagCh2 E.dual.cInf fl' a := by
  intro k _ S p _ r E fl a hS ⟨hfin, x, hx, ha⟩
  have := hS.toIsArithVar.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hsum := fun σ => GlobalTheory.T.dual_flag_bott_chern_sum k S p E.E r E.h E.cInf fl σ hS
  have hfin' : E.h.dual.FlagBcFinite (dualFlag fl) := fun i σ =>
    ne_top_of_le_ne_top ((hsum σ).symm ▸ ENNReal.sum_ne_top.2 fun j _ => hfin j σ)
      (Finset.single_le_sum (f := fun j => ((E.h.dual.stepMet (dualFlag fl) j).met σ).bcMeas
        (VMetric.stepSeq_shortExact (dualFlag fl) j) ((dualFlag fl).isVB j.castSucc)
        ((dualFlag fl).isVB_gr j) univ) (fun _ _ => by simp) (Finset.mem_univ i))
  refine ⟨dualFlag fl, hfin', fun i => x i.rev, fun i =>
    (GlobalTheory.T.dual_flag_graded_isometric k S p E.E r E.h E.cInf fl i).isSelfInter hS.toIsArithVar
      (GlobalTheory.T.self_intersection_dual k S p _ _ hS (hx i.rev)), ?_⟩
  have hbc : E.h.dual.flagBc (dualFlag fl) = E.h.flagBc fl := by
    simp only [VMetric.flagBc, VMetric.bcInt, finsum_eq_sum_of_fintype]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← ENNReal.toReal_sum fun j _ => hfin' j σ, ← ENNReal.toReal_sum fun j _ => hfin j σ, hsum σ]
  rw [ha, show E.dual.h.flagBc (dualFlag fl) = E.h.flagBc fl from hbc]
  congr 1
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl).symm

end GlobalTheory.DualFlag
