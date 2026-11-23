import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem suppPl_emb {D : D7} (V : HSp D) (v : FinPl D) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.WeilParts.SuppPl (pairA D.host.F 0 (singleV D.host.F v 1)) V (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) := by
  intro i j
  let t₁ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (R' := AF D.host.F)
    (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl)
  let t₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
  have key : ∀ x, t₁ (t₂ 1) * t₁ (t₂ x) = t₁ (t₂ x) := fun x => by rw [← map_mul, ← map_mul, one_mul]
  change t₁ (t₂ 1) * (((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
    ((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j
  by_cases e : i = j
  · subst e
    simp only [Matrix.one_apply_eq, mul_one, map_add, map_sub]
    linear_combination key ((HA.mat _ _ _ k).1 i i) - key 1
  · simp only [Matrix.one_apply_ne e, mul_zero, zero_add, sub_zero]
    exact key _

theorem emb_keeps_latHat {D : D7} (V : HSp D) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hL : L.FG)
    (v : FinPl D) {k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v) (y) :
    y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k)).mulVec y ∈
        latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) := by
  have h := GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  rw [GlobalTheory.AdelicU.levelOff_eq] at h
  exact (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL _).1 h.2 y

theorem inertVacuumFixed : ∀ D : D7, InertVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hns : GlobalTheory.WeilParts.NonSplitAt D v (pairA D.host.F 0 (singleV D.host.F v 1)) := ⟨hε, hv⟩
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩)
     hW v _ hns uS uT _ _
    (suppPl_emb S v k) (suppPl_emb T v k')
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T ΛS ΛT hS hT v _ hε _ _
      (emb_keeps_latHat S hS.1.fg v hk) (emb_keeps_latHat T hT.1.fg v hk')) f hf fun u hu => ?_
  obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
  have h1 : 2 • (a • u) = u := by
    rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
  have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
  rwa [h1] at h2

end GlobalTheory.PlaceTensor

end
