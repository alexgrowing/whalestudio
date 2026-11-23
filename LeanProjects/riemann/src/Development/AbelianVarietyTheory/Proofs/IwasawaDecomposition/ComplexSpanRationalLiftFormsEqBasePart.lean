import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.LocalToGlobal.IndefiniteReal.FinrankISupLeSum
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.RatSpan

theorem span_jW_wp : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) = (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim

  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    refine (GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i y).trans ?_
    congr 1
  have hmem : ∀ y, y ∈ (s0Of R F).Wp i p ↔ Z.jW i y ∈ (R.Wp3 i p).comap (Y.mj.eW i) := by
    intro y
    show (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ (R.toCx3 F).Wp i p ↔ _
    exact (Iff.of_eq (congrArg (· ∈ (R.toCx3 F).Wp i p) (hpt y))).trans Iff.rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem y).1 hy
  · intro x hx
    have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have hinj : Function.Injective (Y.mj.eW i) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro d hd
      have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
      have h2 : ‖d‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h hnP.ne'
        · exact h
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
    have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
    set U : Submodule ℂ ((R.toCx3 F).W i) := Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) with hU
    have hUT : U = (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hU, Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨hy, LinearMap.mem_range_self _ _⟩
      · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
          hR.liftHyp0.h3W hR.partsW i p]
        exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw U ((R.toCx3 F).WpK false i p)
          (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
    have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
      rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
      exact LinearMap.mem_range_self _ _
    rw [← GlobalTheory.Mem.LiftTheta.goodForm_span] at hWS
    have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ U := by
      rw [hUT]
      refine ⟨hx, ?_⟩
      have h2 := Submodule.mem_map_of_mem (f := Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) hWS
      rw [Submodule.map_span] at h2
      refine (Submodule.span_le.2 ?_) h2
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨Pi.single k 1, ?_⟩
      have h3 := GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i (Pi.single k 1)
      exact (congrArg ((R.toCx3 F).w0C false i) (cpt_single A3.A.v0.embedding k).symm).trans h3
    let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
      { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
        map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
        map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
    have h4 : Y.mj.eW i x ∈ U.map outL := Submodule.mem_map_of_mem (f := outL) h1
    rw [hU, Submodule.map_span, ← Set.image_comp] at h4
    have h5 : Submodule.span ℂ ((outL ∘ fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) ''
        ((R.toCx3 F).WpK false i p : Set _)) ≤
        (Submodule.span ℂ ((Z.jW i) '' (((R.toCx3 F).WpK false i p : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)) :
          Set (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL)))).map (Y.mj.eW i) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨Z.jW i y, Submodule.subset_span ⟨y, hy, rfl⟩, ?_⟩
      show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
    obtain ⟨x', hx', hxx⟩ := h5 h4
    rw [← hinj hxx]
    exact hx'

end GlobalTheory.Mem.R3.RatSpan
