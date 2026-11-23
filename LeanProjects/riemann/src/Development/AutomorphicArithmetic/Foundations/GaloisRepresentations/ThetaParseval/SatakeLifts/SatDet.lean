import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem range_map_eq {α : Type} (t : ℕ) (F : ℕ → α) :
    (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => F (i : ℕ)) = (Finset.range t).val.map F := by
  have h : (Finset.range t).val = (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => (i : ℕ)) := by
    have h' : Finset.range t = (Finset.univ : Finset (Fin t)).map Fin.valEmbedding := by
      ext i
      simp only [Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
      exact ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩
    rw [h', Finset.map_val]
    rfl
  rw [h, Multiset.map_map]
  rfl

theorem UpperTheory.Gal.TP.Loc.satDet :
    UpperTheory.Gal.TP.Loc.SatDet := by
  intro K _ _ w t c hc ϖ hϖ
  have hv : valuation (w.adicCompletion K) (ϖ : w.adicCompletion K) = uniformizer (w.adicCompletion K) :=
    GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ
  have hord : Formalism.UG.ordV K w (ϖ : w.adicCompletion K) = 1 := by
    rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v (ϖ : w.adicCompletion K) = _ from hϖ]
    rfl
  have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K w t _ _ _ (hasSatake_detRep hc hv)
  have hm : GlobalTheory.LFun.seg w (c ϖ) t = (Finset.univ : Finset (Fin t)).val.map
      (fun i : Fin t => c ϖ * absPow (w.adicCompletion K) (((i : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ) := by
    rw [GlobalTheory.LFun.seg, ← range_map_eq]
    refine Multiset.map_congr rfl fun i _ => ?_
    congr 1
    ext
    rw [GlobalTheory.SatInd.val_absPow_completion, hord]
    simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Formalism.UG.qV]
    congr 1
    push_cast
    ring
  rw [hm]
  exact h
