import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamDim

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : V ≃+ Tw.sub s V :=
    { toFun := fun x => ⟨Tw.mk s (x : E), x.2⟩
      invFun := fun y => ⟨Tw.out (y : Tw s E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hi : Function.Bijective (cj s) :=
    ⟨fun a b h => by simpa [cj_cj] using congrArg (cj s) h, fun z => ⟨cj s z, cj_cj s z⟩⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hi (fun r m => by
    apply Subtype.ext
    show r • (m : E) = cj s (cj s r) • (m : E)
    rw [cj_cj])
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := by
  ext x; exact Iff.rfl

theorem finrank_comap_of_inj {M E : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup E] [Module ℂ E]
    (f : M →ₗ[ℂ] E) (hf : Function.Injective f) (S : Submodule ℂ E) :
    Module.finrank ℂ (S.comap f) = Module.finrank ℂ (S ⊓ LinearMap.range f : Submodule ℂ E) := by
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf (S.comap f)), Submodule.map_comap_eq, inf_comm]

end GlobalTheory.Mem.R3.LamDim

open GlobalTheory.Mem.R3.LamDim in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  set s := twAt D.what₂.embLL A3.A.v0 with hs

  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero, zero_pow two_ne_zero] at h1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

  have hrg : LinearMap.range (Y.mj.eW i) = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [Y.mj.eW_range i, hH.aux.levelW false i (sg0 D A3.A)]

  have hw : LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) •
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).1 ∈ _
      exact Submodule.smul_mem (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) _
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).2
    · intro x hx
      have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
          Submodule.comap (Tw.mkL s (R.HW i (sg0 D A3.A)).H) (LinearMap.range ((R.toCx3 F).w0C false i)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
      exact hle hx
  have hD := hH.prim.dimParts i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have key := CxData.finrank_Ep (R.toCx3 F) F.cr false (hR.wf false) (hR.what₂ false).1 (hR.rowHyp false).h3
    (hR.partsE false) p
  have key2 : Module.finrank D.what₂.LL ((s0Of R F).Ep p) =
      Module.finrank ℂ ((R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) := key
  rw [key2, ← hD, finrank_comap_of_inj _ hinj, hrg, hw]
  show _ = Module.finrank ℂ (Tw.sub s (R.Wp3 i p) ⊓ Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) : Submodule ℂ _)
  rw [← twSub_inf, finrank_twSub]
