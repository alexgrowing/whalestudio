import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaMulRationalVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLiftLabelEqFinrankFace3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.ThRead.L0

set_option maxHeartbeats 1000000 in

theorem eW_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, ∀ y, Y.mj.eW i (Z.jW i y) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ _ i y
  exact (Z.jW_read i y).trans (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _))

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.ThRead.L0

theorem eW_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, Function.Injective (Y.mj.eW i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ _ i
  exact GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i)

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.ThRead.L0

theorem li_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, LinearIndependent ℂ (fun k => Z.jW i (Pi.single k 1)) ∧
    Submodule.span ℂ (Set.range fun k => Z.jW i (Pi.single k 1)) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i
  have he := eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hc : (Y.mj.eW i ∘ fun k => Z.jW i (Pi.single k 1)) = fun k =>
      GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1) :=
    funext fun k => eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i _
  refine ⟨LinearIndependent.of_comp (Y.mj.eW i) ?_, ?_⟩
  · rw [hc]; exact GlobalTheory.Mem.LiftTheta.goodForm_li R.toRealDat F.lv2 hH.prim.unif false i
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp, hc]
    exact (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
      ((hH.aux.levelW false i _).trans (Y.mj.eW_range i).symm)

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.ThRead.L0

theorem chiKs_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, (R.FW i).ChiKs := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.ThRead.L0

set_option maxHeartbeats 1000000 in

theorem lat_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m,
    OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (Z.jW i) ((A3.indefDown (s0Of R F)).M i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i
  have he := eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hli := (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).1
  have hej := eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hI := hH.aux.integral i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1)
    (chiKs_of_pins D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i) F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
    (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]; rfl⟩
  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have himg : Y.mj.eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier =
      (R.FW i).j (sg0 D A3.A) '' {y | y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy1, hy2, e⟩ := (Y.mj.eW_lat i x).1 hx
      exact ⟨y, ⟨hy1, hy2⟩, e.symm⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyM : y ∈ (R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
        rw [← hspan]; exact Submodule.subset_span ⟨hy1, hy2⟩
      obtain ⟨c, -, hcy⟩ := (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i _).1 ⟨y, hyM, rfl⟩
      exact ⟨Z.jW i c, (Y.mj.eW_lat i _).2 ⟨y, hy1, hy2, (hej c).trans hcy⟩, (hej c).trans hcy⟩
  refine GlobalTheory.Mem.LiftTheta.oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (Y.mj.eW i) he (Z.jW i)
    (GlobalTheory.Mem.LiftTheta.semi_injective _ hli) _
    ((R.FW i).j (sg0 D A3.A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) : Set _)) (fun y => ?_) ?_
  · refine (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i y).trans ?_
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).trans h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).symm.trans h⟩⟩
  · rw [himg, ← hspan]
    exact closure_span_eq (σ := D.what₂.embLL) ((R.FW i).j (sg0 D A3.A)).toAddMonoidHom
      (fun b x => by
        rw [← hsg]
        show (R.FW i).j _ (b • x) = _
        rw [← algebraMap_smul D.what₂.LL b x, map_smulₛₗ]
        rfl) _

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.ThRead.L0

set_option maxHeartbeats 2000000 in

theorem theta_of (T1 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x))) (T2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0) : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) x,
    D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
      Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t x
  change Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL at x
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h5 := hR.lifts0.1
  have hr := hR.ratTh
  have hOk := hH.ok.ok2
  apply eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  refine (T1 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t x).trans ?_
  refine Eq.trans ?_ (eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i _).symm
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hsub : ∀ a b, liftForm A3.A F.P0 F.ψ0 i t (a - b) = liftForm A3.A F.P0 F.ψ0 i t a - liftForm A3.A F.P0 F.ψ0 i t b :=
    fun a b => by unfold liftForm; rw [Matrix.mulVec_sub, map_sub]
  have h1 : R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)))) := by
    have h := T2 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
      (x - lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)) (fun z => by rw [map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self])
    rwa [hsub, map_sub, map_sub, sub_eq_zero] at h
  rw [h1]
  have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false h5 hr i t
    (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)
  have h3 := GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t
    (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)
  have h4 := GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i
    ((R.toCx3 F).liftMat F.cr false i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
  have key := h4.symm.trans (h2.trans (by
    show R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) _) = _
    have h3' : F.cr.toL (R.toCx3 F).zs false i t (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x) =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)) :=
      h3.symm
    rw [hP.phs i, one_smul, h3']
    rfl))
  exact (congrArg Tw.out key).symm

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.ThRead.L0

set_option maxHeartbeats 1000000 in

theorem thDef3_thTheta : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F →  ThDef3 D A3.A (A3.indefDown (s0Of R F)) Y.tup Y.eMt Z.jW ∧ ∀ (i : Fin D.R.m) (t : T) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) = Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  exact ⟨⟨fun i => (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).1,
    fun i => (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).2, lat_of D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH⟩,
    theta_of GlobalTheory.Mem.ThetaRead3.L0.thetaP_read GlobalTheory.Mem.ThOrth.L0.thG_eq_zero_of_orth D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH⟩

end GlobalTheory.Mem.ThRead.L0

namespace GlobalTheory.Mem.LiftOnto.L0

set_option maxHeartbeats 1000000 in

theorem thetaMap_surjective : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t _
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  obtain ⟨hTh, hθ⟩ := GlobalTheory.Mem.ThRead.L0.thDef3_thTheta D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hTh.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  refine ⟨D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z)), ?_⟩
  have hz' : lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) = z := by
    refine (Matrix.mulVec_mulVec _ _ _).trans ?_
    exact (congrArg (fun M => M *ᵥ z) hp.1).trans (Matrix.one_mulVec z)
  show _ = Z.jW i (Pi.single k 1)
  rw [hθ i t]
  exact congrArg (Z.jW i) ((congrArg (((A3.indefDown (s0Of R F)).θ i t).mulVec) hz').trans hz)

end GlobalTheory.Mem.LiftOnto.L0

namespace GlobalTheory.Mem.R3.LamMetric.L0

set_option maxHeartbeats 2000000 in

theorem inner_theta_rat_eq_lam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) a b, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p a b hyp
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT : ∀ c, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding c)) = Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c)))) := by
    intro c
    rw [GlobalTheory.Mem.ThetaRead3.L0.thetaP_read D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t, CxData.tC_cpt_eq]
    show Tw.out (R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) _)) = _
    have h3 := GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t c
    have h3' : ((crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc).toL (R.toCx3 F).zs false i t) c = liftForm A3.A F.P0 F.ψ0 i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c) := h3.symm
    rw [hP.phs i, one_smul]
    show R.thG i t (R.jV i t (((crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc).toL (R.toCx3 F).zs false i t) c)) = _
    exact congrArg (fun z => R.thG i t (R.jV i t z)) h3'
  have hW : (R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a) ∈ (R.toCx3 F).Wp i p := by
    show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a)) ∈ R.Wp3 i p
    exact (congrArg (· ∈ R.Wp3 i p) (hT a)).mpr hyp
  have hA := hR.lifts0.2 i t p a hW b
  have hL : ⟪(R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a), (R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding b)⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) ⟪Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))⟫_ℂ := by
    refine (Tw.inner_eq (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) _ _).trans ?_
    exact congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrArg₂ (fun x y => ⟪x, y⟫_ℂ) (hT a) (hT b))
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin ((lv (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs) false).dZ i t))) ((lv (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs) false).XT i t) A3.fam3.base3.v0 a b = A3.A.v0.embedding (star a ⬝ᵥ ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) *ᵥ b) := by
    have hm : metOf ((A3.A.fam.L i t).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t) A3.A.v0) = ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)).map A3.A.v0.embedding :=
      (BlockDat.XQ_herm hOk.conj (hOk.lifts i t) hOk.irr).2
    show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((A3.A.fam.L i t).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) A3.A.v0 a b = _
    rw [Formalism.L2.DIV.majAt_eq, hm]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : A3.A.v0.embedding (star (a k)) = starRingEnd ℂ (A3.A.v0.embedding (a k)) := hOk.conj (a k)
    rw [hc]
    rfl
  have hU : ⟪(D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = D.what₂.embLL (star a ⬝ᵥ ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) *ᵥ b) := by
    have hf := (Y.formsL i t).inner (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)
    have hl := BlockDat.lf_lE_form (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1)
    refine hf.trans ?_
    congr 1
    exact (GlobalTheory.Mem.LiftForms.hform_mulVec (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) a b).trans (congrArg (fun M => star a ⬝ᵥ M *ᵥ b) hl)
  have hv : ∀ c, A3.A.v0.embedding c = cj (twAt D.what₂.embLL A3.A.v0) (D.what₂.embLL c) := by
    intro c
    rw [emb_eq D.what₂.embLL A3.A.v0 c, sgAt_mk _ R.hv0]
  have hN := GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i) (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))
  have h1 : cj (twAt D.what₂.embLL A3.A.v0) (((RealDat.nP F.lv2 false : ℝ) : ℂ) * ⟪(D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))), (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))⟫_ℂ) = ((RealDat.nP F.lv2 false * R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * cj (twAt D.what₂.embLL A3.A.v0) ⟪(D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ := by
    rw [← hN, ← hL, hA, hmaj, hv, hU]
    rfl
  have h2 := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) h1
  rw [cj_cj, map_mul, cj_ofReal, cj_cj] at h2
  have hnp : ((RealDat.nP F.lv2 false : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (RealDat.nP_pos (F := F.lv2) false).ne'
  apply mul_left_cancel₀ hnp
  rw [h2]
  push_cast
  ring

end GlobalTheory.Mem.R3.LamMetric.L0

namespace GlobalTheory.Mem.KerSpan.L0
variable {K : Type} [Field K] {σ : K →+* ℂ}

set_option maxHeartbeats 2000000 in

theorem orth_ker_thetaP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT := GlobalTheory.Mem.ThRead.L0.thDef3_thTheta D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hΘ : ∀ a, ((A3.indefDown (s0Of R F)).θ i t) *ᵥ a = 0 → a = 0 := by
    intro a ha
    have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false hR.lifts0.1 hR.ratTh i t a
    have h6 := CxData.tC_cpt_eq (R.toCx3 F) F.cr false i t a
    have ha' : (R.toCx3 F).liftMat F.cr false i t *ᵥ a = 0 := ha
    have h7 : (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) = (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding 0) := by
      rw [h6, ← h2, ha']
      have hz : ∀ {k : ℕ}, cpt A3.fam3.base3.v0.embedding (0 : Fin k → D.what₂.LL) = 0 := fun {k} => by
        funext l; simp [cpt]
      simp only [hz, map_zero]
    exact cpt_injective _ ((hR.lifts0.1 i t).1 h7)
  exact GlobalTheory.Mem.KerSpan.orth_ker_eq_span _ _ (Y.formsL i t).inner (Y.formsL i t).span _ _ hp
    (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (Z.jW i) (hT.1.li i) _ hΘ (fun x => hT.2 i t x)

end GlobalTheory.Mem.KerSpan.L0

namespace GlobalTheory.Mem.R3.PartSpan.L0

set_option maxHeartbeats 4000000 in

theorem mem_span_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p x hx hW
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have e1 := GlobalTheory.Mem.ThetaRead3.L0.thetaP_read D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  have h5 := hR.lifts0.1
  let Φ : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H :=
    (Y.mj.eW i).comp (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1))
  let u := ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap).comp
    (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVecLin
  let m : (R.HW i (sg0 D A3.A)).H →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.toCx3 F).W i := Tw.mkL (twAt D.what₂.embLL A3.A.v0) _
  have hcon : ∀ a, m (Φ (u a)) =
      (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) := by
    intro a
    refine Eq.trans ?_ ((R.toCx3 F).tC_cpt_eq F.cr false i t a).symm
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))))) =
      R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) (F.cr.toL (R.toCx3 F).zs false i t a))
    have h3' : F.cr.toL (R.toCx3 F).zs false i t a =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) :=
      (GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t a).symm
    rw [hP.phs i, one_smul, e1, h3']
    rfl

  have hsing : ∀ k : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)),
      cpt A3.fam3.base3.v0.embedding (Pi.single k (1 : D.what₂.LL)) = Pi.single k 1 := by
    intro k
    funext j
    by_cases h : j = k
    · subst h; simp [cpt]
    · simp [cpt, Pi.single_apply, h]
  have hsum : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, m (Φ (∑ k, c k • u (Pi.single k 1))) =
      (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) := by
    intro c
    have hc : (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        ∑ k, cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    refine Eq.trans ?_ (congrArg ((R.toCx3 F).tC F.cr false i t) hc).symm
    rw [map_sum, map_sum]
    refine Eq.trans ?_ (map_sum ((R.toCx3 F).tC F.cr false i t) (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    refine Eq.trans ?_ (map_smul ((R.toCx3 F).tC F.cr false i t) _ _).symm
    exact congrArg (fun z => cj (twAt D.what₂.embLL A3.A.v0) (c k) • z)
      ((hcon (Pi.single k 1)).trans (congrArg ((R.toCx3 F).tC F.cr false i t) (hsing k)))

  have hinj : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0 := by
    intro c hc
    have h0 : (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        0 := by
      rw [← hsum c]
      show Tw.mk _ (Φ _) = 0
      rw [hc]
      rfl
    have h1 := (h5 i t).1 (h0.trans (map_zero _).symm)
    funext k
    have hk := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrFun h1 k)
    rw [Links.cj_cj] at hk
    exact hk.trans (map_zero (cj (twAt D.what₂.embLL A3.A.v0)))
  have hw0 := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
  have hC : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≤
      Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) := by
    have hSpW : Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) ≤
        (R.toCx3 F).Wp i p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      exact ha
    have hle := finrank_le_cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).w0C false i) hw0
      (Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})))
      ((R.toCx3 F).WpK false i p) (fun y hy => by
        obtain ⟨a, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) h5 hR.ratTh i t).2 y
        have hk := (R.toCx3 F).key_lift F.cr false h5 hR.ratTh i t a
        have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMat F.cr false i t *ᵥ a)) ∈
            (R.toCx3 F).Wp i p := hy
        rw [hk, ← hcon a] at hy'
        rw [hk, ← hcon a]
        exact Submodule.subset_span ⟨Φ (u a), ⟨u a, ⟨a, hy', rfl⟩, rfl⟩, rfl⟩)
    rw [(R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 h5 hR.ratTh hR.liftHyp0.h3W hR.partsW i p] at hle
    have heq := Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hSpW) hle
    exact heq.symm.le.trans inf_le_left
  have hspan : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ R.Wp3 i p →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y}) := by
    intro c hc
    have hm : m (Φ (∑ k, c k • u (Pi.single k 1))) ∈
        (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      refine ⟨hc, ?_⟩
      rw [← (h5 i t).2]
      exact ⟨_, (hsum c).symm⟩
    have h1 := hC hm
    rw [← Submodule.map_span] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
    have hwe' : w = Φ (∑ k, c k • u (Pi.single k 1)) := hwe
    rw [← hwe']
    exact hw
  exact mem_span_rat u Φ (R.Wp3 i p) hinj hspan x hx hW

end GlobalTheory.Mem.R3.PartSpan.L0

end
