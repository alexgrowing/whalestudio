import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric

set_option maxHeartbeats 2000000 in

theorem inner_theta_rat_eq_lam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) a b, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p a b hyp
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT : ∀ c, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding c)) = Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c)))) := by
    intro c
    rw [GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t, CxData.tC_cpt_eq]
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

end GlobalTheory.Mem.R3.LamMetric
