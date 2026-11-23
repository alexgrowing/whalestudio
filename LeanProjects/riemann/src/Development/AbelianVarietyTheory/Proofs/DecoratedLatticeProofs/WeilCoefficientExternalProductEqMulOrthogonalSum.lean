import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.BoxCoef

theorem wcoef_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ νB 𝓕B νW 𝓕W νH 𝓕H, IsCovolOne (ratL B A) νB 𝓕B → IsCovolOne (ratL W A) νW 𝓕W → IsCovolOne (ratL H A) νH 𝓕H → ∀ Φ Φ', IsThetaFunO ψ A W Φ → IsThetaFunO ψ A H Φ' → ∀ g, wcoef omB νB 𝓕B (o.boxT A Φ Φ') (o.boxT A Φ Φ') g = wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H Φ' Φ' g := by
  intro D ψ A B W H o χA χW omB omW omH hB hW hH νB 𝓕B νW 𝓕W νH 𝓕H cB cW cH Φ Φ' hΦ hΦ' g
  have hψ := hB.std
  have hB' : IsWeilDatumO ψ A B χA (χW * 1) omB := by rwa [mul_one]
  have hom := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ B W H o A).om_box χA χW 1 omB omW omH hB' hW hH g 1 1 Φ Φ'
    hΦ hΦ'
  have e1 : o.emb ((1 : GA D W), (1 : GA D H)) = 1 := map_one o.emb
  rw [e1] at hom
  have hF1t : IsThetaFunO ψ A W (omW (g, 1) Φ) := hW.om_pres _ _ hΦ
  have hF2t : IsThetaFunO ψ A H (omH (g, 1) Φ') := hH.om_pres _ _ hΦ'
  simp only [wcoef, ip]
  rw [hom]
  haveI := GlobalTheory.WeilSliceUnit.borel_Mx (D := D) B.rank A.rank
  haveI := GlobalTheory.WeilSliceUnit.borel_Mx (D := D) W.rank A.rank
  haveI := GlobalTheory.WeilSliceUnit.borel_Mx (D := D) H.rank A.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D B.rank A.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D W.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D H.rank A.rank
  haveI := cW.1
  haveI := cH.1
  let e : WO A B ≃ₜ (WO A W × WO A H) :=
    { (o.resT A).toEquiv with continuous_toFun := o.continuous_resT A, continuous_invFun := o.continuous_resT_symm A }
  let em := e.toMeasurableEquiv
  let μP : Measure (WO A W × WO A H) := νW.prod νH
  let μ' : Measure (WO A B) := μP.map em.symm
  haveI : μ'.IsAddHaarMeasure :=
    (o.resT A).symm.isAddHaarMeasure_map μP (o.continuous_resT_symm A) (o.continuous_resT A)
  have hmp : MeasurePreserving em μ' μP := ⟨em.measurable, em.map_map_symm⟩
  have hprod := GlobalTheory.WeilSliceUnit.isAddFundamentalDomain_prod cW.2.1 cH.2.1
  have hmem : ∀ γ : (ratL W A).prod (ratL H A), (o.resT A).symm (γ : WO A W × WO A H) ∈ ratL B A := fun γ => by
    rw [o.mem_ratL_resT, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 γ.2
  have hP : IsAddFundamentalDomain (ratL B A) (em ⁻¹' (𝓕W ×ˢ 𝓕H)) μ' := by
    refine hprod.preimage_of_equiv hmp.quasiMeasurePreserving (e := fun γ => ⟨_, hmem γ⟩)
      ⟨fun γ γ' h => ?_, fun h => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((o.resT A).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resT A h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resT A h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resT A).symm_apply_apply h
    · change o.resT A ((o.resT A).symm (γ : WO A W × WO A H) + x) = (γ : WO A W × WO A H) + o.resT A x
      rw [map_add, AddEquiv.apply_symm_apply]
  have hvol : μ' (em ⁻¹' (𝓕W ×ˢ 𝓕H)) = 1 := by
    rw [← em.map_apply, hmp.map_eq, Measure.prod_prod, cW.2.2, cH.2.2, one_mul]
  have hcov : IsCovolOne (ratL B A) μ' (em ⁻¹' (𝓕W ×ˢ 𝓕H)) := ⟨inferInstance, hP, hvol⟩
  have hper := GlobalTheory.Size.mul_conj_periodic hψ (o.isThetaFunO_boxT hF1t hF2t) (o.isThetaFunO_boxT hΦ hΦ')
  refine (covolOne_integral_eq cB hcov (fun w => o.boxT A (omW (g, 1) Φ) (omH (g, 1) Φ') w * conj (o.boxT A Φ Φ' w)) hper).symm.trans ?_
  have hfun : (fun w => o.boxT A (omW (g, 1) Φ) (omH (g, 1) Φ') w * conj (o.boxT A Φ Φ' w)) =
      fun w => (fun y : WO A W × WO A H =>
        (omW (g, 1) Φ y.1 * conj (Φ y.1)) * (omH (g, 1) Φ' y.2 * conj (Φ' y.2))) (em w) := by
    funext w
    show omW (g, 1) Φ (o.resT A w).1 * omH (g, 1) Φ' (o.resT A w).2 * conj (Φ (o.resT A w).1 * Φ' (o.resT A w).2) =
      omW (g, 1) Φ (o.resT A w).1 * conj (Φ (o.resT A w).1) * (omH (g, 1) Φ' (o.resT A w).2 * conj (Φ' (o.resT A w).2))
    rw [map_mul]; ring
  rw [hfun]
  refine (hmp.setIntegral_preimage_emb em.measurableEmbedding (fun y : WO A W × WO A H =>
    (omW (g, 1) Φ y.1 * conj (Φ y.1)) * (omH (g, 1) Φ' y.2 * conj (Φ' y.2))) (𝓕W ×ˢ 𝓕H)).trans ?_
  rw [← Measure.prod_restrict]
  exact integral_prod_mul (fun u => omW (g, 1) Φ u * conj (Φ u)) (fun v => omH (g, 1) Φ' v * conj (Φ' v))

end GlobalTheory.Core.Rk.BoxCoef

end
