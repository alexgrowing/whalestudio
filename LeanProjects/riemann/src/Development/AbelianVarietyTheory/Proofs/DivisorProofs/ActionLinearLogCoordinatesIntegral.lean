import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

theorem actSt : ActSt := by
  intro C _ _ v d R _ _ O _ _ B hB σ _ a

  have hφ0 : ∀ i, constantCoeff (B.actK C a i) = 0 := by
    intro i
    show constantCoeff (MvPowerSeries.map (algebraMap R C) (B.A.act a i)) = 0
    rw [MvPowerSeries.constantCoeff_map, GlobalTheory.FBMap.nc_act B.A a i, map_zero]

  have hhom : comp1 (B.actK C a) (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F =
      addOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F (comp1 (B.actK C a) (pt C (n := 2) d 0))
        (comp1 (B.actK C a) (pt C (n := 2) d 1)) := by
    have h := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).hom a
    rw [GlobalTheory.LawLog.add_pt] at h
    exact h

  have hcomp := GlobalTheory.FactorDepth.logOf_comp_hom _ _ (B.actK C a) hφ0 hhom
  have h0 : ∀ e, constantCoeff (subst (oneVar C d) (B.actK C a e)) = 0 := fun e =>
    constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hφ0 e)
  have hl : ∀ e, subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e) =
      ∑ f, dAct C B a e f • (fglOf hB).lg f := by
    intro e
    calc subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e)
        = subst (oneVar C d)
            (comp1 (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G)) (B.actK C a) e) :=
          GlobalTheory.LawLog.subst_oneVar (oneVar C d) cc_oneVar (B.actK C a) hφ0
            (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G) e)
      _ = ∑ f, dAct C B a e f • (fglOf hB).lg f := by
          rw [hcomp]
          dsimp only
          rw [← coe_substAlgHom hs_oneVar, map_sum]
          simp only [map_smul, coe_substAlgHom]
          exact Finset.sum_congr rfl fun f _ => rfl

  have hexp : ∀ w : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      expPt (fglOf hB) (mv (dAct C B a) w) =
        fun i => subst (fun q : Fin 1 × Fin d => expPt (fglOf hB) w q.2) (B.actK C a i) := by
    intro w hw
    have hsE : HasSubst (fun f => subst w (GlobalTheory.FGDepth.expOf (fglOf hB) f)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun f => cc_expPt (fglOf hB) hw f
    funext i
    have key := GlobalTheory.FactorDepth.exp_eq_of_log_hom (fglOf hB) (fglOf hB) _ h0 (dAct C B a) hl
      (mv (dAct C B a) w) w hw (fun e => rfl) i
    show subst (mv (dAct C B a) w) (GlobalTheory.FGDepth.expOf (fglOf hB) i) = _
    rw [key, subst_comp_subst_apply hs_oneVar hsE]
    congr 1
    funext q
    exact subst_X hsE q.2
  refine ⟨hexp, fun w hw => ⟨cc_mv (dAct C B a) hw.1, fun i => ?_⟩⟩

  rw [hexp w hw.1]
  exact ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hB.2.1 a i) (fun q => hw.2 q.2)
    (fun q => cc_expPt (fglOf hB) hw.1 q.2)

end GlobalTheory.IsoTriv
