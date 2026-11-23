import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.ExistsCharNotOnto
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.RealIndexBound

open Formalism.BasicNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.OntoChain GlobalTheory.RealIndexBoundProbe

theorem rankRows_cx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (wf : (lv (fc X.zs) b).WF) (hp : (lv (fc X.zs) b).Pos)
    (ht : (lv (fc X.zs) b).Types) (h3 : X.H3 cr b) (h3W : X.H3W cr b) (h5 : X.H5 cr b) (hr : X.RATth cr b)
    (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (hd : (X.data cr b).DimensionsOfPartsAgree) : RankRows (X.data cr b) := by
  refine ⟨hp, fun j => ?_⟩
  have hb := X.liftMat_bij cr b hk he hn h5 hr j Bs.μ0
  have h1 := sum_finrank ((lv (fc X.zs) b).Qp Bs.μ0) wf.Qp_indep wf.Qp_top
  have h2 := sum_finrank ((lv (fc X.zs) b).Zp j Bs.μ0) (wf.Zp_indep _) (ht _)
  rw [Module.finrank_fin_fun] at h1 h2
  have h0 : (lv (fc X.zs) b).dZ j Bs.μ0 = X.dW b j := dim_of_bij _ hb
  show X.dW b j = (lv (fc X.zs) b).dQ Bs.μ0
  rw [← h0, ← h1, ← h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : (lv (fc X.zs) b).Qp Bs.μ0 p = X.Ep cr b p := Submodule.ext fun x => h3 p x
  have e2 : (lv (fc X.zs) b).Zp j Bs.μ0 p = (X.WpK b j p).comap (X.liftMat cr b j Bs.μ0).mulVecLin := by
    ext x
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply, CxData.mem_WpK, X.key_lift cr b h5 hr]
    exact h3W j p x
  rw [e1, e2, finrank_comap_bij _ hb]
  exact hd j p

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem rankRows_of_links {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (hSt : R.LStable F) (hBl : R.LBlock F)
    (hP : R.LPos F) (hT : R.LTypes F) (hE : R.LPartsE F) (hW : R.LPartsW F) (h5 : R.LTheta F) (hr : R.LRatTh F)
    (hU : R.LUnif) (hd : R.LDims F) : RankRows ((R.toCx F).data F.cr false) :=
  rankRows_cx (R.toCx F) F.cr false (A.side_WF hOk F.P0 F.ψ0 _ hSt hBl hsep) (hP false) (hT false) (hE false) (hW false)
    (h5 false) (hr false) (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false) (hd false)

theorem not_onto_of_char_alone (h : R.Char F) {w : HeightOneSpectrum (𝓞 D.what₂.LL)} (hw : w ∈ R.twPl) :
    ∃ R' : RealDat D A Ks, R'.Char F ∧ R'.mu = R.mu ∧ R'.twPl = R.twPl ∧ ∀ C CH, ¬ R'.LOnto F C CH :=
  exists_char_not_onto h hw ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩

variable {P : Type} [Group P] [Finite P] {c : OnConst}

theorem onto_of_coord (O : OnObj ((R.toCx F).data F.cr false) P c) (C CH : ℝ)
    (hRk : RankRows ((R.toCx F).data F.cr false)) (hC : TieCoord O)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood (R.num F C CH) O) (hR : LeafDepthRam (R.num F C CH) O) (h2p : LeafDepth2 (R.num F C CH) O)
    (hL : LeafDepthLevel (R.num F C CH) O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (R.num F C CH) O) (hCE : c.CE ≤ C) (tE1 : ErrorConstantMatchesDefinition (R.num F C CH) O C) :
    (withErr R O.errOn).LOnto F C CH ∧ (TieErr O → R.LOnto F C CH) :=
  ⟨on_built (R.num F C CH) O C hRk hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad
      hJS hJE hCE tE1,
    on_of_leaves (R.num F C CH) O C hRk hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX
      hBad hJS hJE hCE tE1⟩

theorem onto_built {s : ℕ} (c : OnConst) (a : ChainArgs D.what₂.LL (Fin D.R.m) R.nW) (C CH : ℝ)
    (hOk : A.fam.Ok s) (hC : R.Char F) (hI : R.LIntegral) (hRk : RankRows ((R.toCx F).data F.cr false))
    (hY : LeafYBound (onOf R F c a))
    (hSp : LeafSpan (onOf R F c a)) (hS : LeafLemmaS (onOf R F c a)) (hT0 : LatticeIndexBoundAtPairs (onOf R F c a))
    (hD : LeafData (onOf R F c a)) (hJ : LeafRankJ (onOf R F c a)) (h2 : LeafTW2 (onOf R F c a))
    (h1 : LeafTW1 (onOf R F c a)) (hSh : LeafShareI (onOf R F c a)) (hBS : LeafBadShare (onOf R F c a))
    (hG : LeafDepthGood (R.num F C CH) (onOf R F c a)) (hR : LeafDepthRam (R.num F C CH) (onOf R F c a))
    (h2p : LeafDepth2 (R.num F C CH) (onOf R F c a)) (hL : LeafDepthLevel (R.num F C CH) (onOf R F c a))
    (hPg : LeafPage (onOf R F c a)) (hSz : LeafSizes (onOf R F c a)) (hX : LeafX (onOf R F c a))
    (hBad : LeafBad (onOf R F c a)) (hJS : LeafJSum (onOf R F c a)) (hJE : LeafJExp (R.num F C CH) (onOf R F c a))
    (hCE : c.CE ≤ C) (tE1 : ErrorConstantMatchesDefinition (R.num F C CH) (onOf R F c a) C) :
    ((withErr R (onOf R F c a).errOn).Char F ∧ (withErr R (onOf R F c a).errOn).LOnto F C CH) ∧
      (TieErr (onOf R F c a) → R.LOnto F C CH) :=
  have h := onto_of_coord (onOf R F c a) C CH hRk (tieCoord c a hOk hC.grp.levels hC.tup.mu_conj)
    (leafMackey c a hC.grp.levels) (leafSup c a hI) (leafProj c a hOk.irr) hSp hS hT0 hD hJ (leafIdentity c a hOk) h2 h1 hSh
    (leafIndexU c a hC.grp.record hY) hBS (leafUnip c a hC.grp.record) hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1
  ⟨⟨char_withErr hC _, h.1⟩, h.2⟩

end Any

section Block

open scoped Matrix

variable {K : Type} [Field K] [NumberField K] [StarRing K] {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms}
  {v0 : InfinitePlace K} {s : ℕ}

theorem lPr_eq_zero (h : BlockHyp B ℓ v0 s) (k : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K)
    (hk : ∀ y, hform B.S.H ((B.fE ℓ Z).mulVec y) ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec k) = 0) : (B.lPr ℓ Z).mulVec k = 0 := by
  set u := (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec k with hu
  have h1 : ((B.fE ℓ Z)ᴴ * B.S.H).mulVec u = 0 := by
    funext i
    have := hk (Pi.single i 1)
    rw [RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] at this
    simpa [← Pi.single_star] using this
  have h2 : (B.vE ℓ)ᴴ * B.S.H * (B.vE ℓ * B.vPr ℓ) = (B.vE ℓ)ᴴ * B.S.H := by
    have := (BlockDat.lf_v_proj h).1.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h3 : (B.zE ℓ Z)ᴴ * B.HV ℓ * B.vPr ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.fE ℓ Z)ᴴ * B.S.H) := by
    rw [BlockDat.lf_HV_eq, Matrix.mul_smul, Matrix.smul_mul, BlockDat.fE, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      Matrix.mul_assoc _ (B.vE ℓ), h2, Matrix.mul_assoc]
  rw [BlockDat.lPr, ← Matrix.mulVec_mulVec, ← hu, BlockDat.Pq, orthPr, Matrix.mul_assoc, h3, ← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, h1, smul_zero, Matrix.mulVec_zero]

end Block

section ClassSum

open GlobalTheory.OnTies Formalism.IndefR.Mult Formalism.IndefR.FWT

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

variable (R) in

def PhasedLift (ph : Fin D.R.m → ℂ) : Prop :=
  ∀ i t x, (R.HW i (sg0 D A)).e (R.thG i t x) = ph i • postOn _ (R.eWf i (sg0 D A)) (R.thF i t x)

theorem phasedLift_one (h : R.thP_thG) : PhasedLift R fun _ => 1 := fun i t x => by rw [one_smul]; exact h i t x

theorem adForm_goodOp (hU : R.LUnif) (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) :
    adForm R i (goodOp R i x) = postOn _ (R.eWf i (sg0 D A)) (adForm R i x) := by
  have h := (hU i (sg0 D A)).2.2
  unfold adForm goodOp
  rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  have e : ∀ T : MMap (R.MW i (sg0 D A)), postOn _ (R.eWf i (sg0 D A)) T = ∑ g, RealDat.eC (A := A) (sg0 D A) g •
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) T := fun T => by
    ext v y
    simp [postOn, RealDat.eWf, gaL, LinearMap.sum_apply]
    rfl
  rw [e]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, map_smul, h, smul_smul, map_mul, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]
  rfl

theorem j_injective (hU : R.LUnif) (i : Fin D.R.m) : Function.Injective ((R.FW i).j (sg0 D A)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra h0
  have := (hU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)
  exact this.ne_zero 0 hx

theorem inner_jV (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) (f g : A.fam.amb.FL i t) :
    inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.fam.L i t).S.csum f.1 g.1) := by
  refine ((h1 i t).2.2 (R.jV i t f) (R.jV i t g)).trans ?_
  refine (congrArg₂ (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)
    (h2 i t f) (h2 i t g)).trans ?_
  exact GlobalTheory.PresBasic.isom (R.B.L i t).pres f g

theorem csum_eq_zero (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) {f g : A.fam.amb.FL i t}
    (hf : f ∈ liftSub R F i t) (hg : R.thG i t (R.jV i t g) = 0) : (A.fam.L i t).S.csum f.1 g.1 = 0 := by
  obtain ⟨w, hw⟩ : (R.toCx F).jL i t f ∈ LinearMap.range (LinearMap.adjoint ((R.toCx F).θ' i t)) := hf
  have h3 : inner ℂ ((R.toCx F).jL i t f) ((R.toCx F).jL i t g) = 0 := by
    have h4 : (R.toCx F).θ' i t ((R.toCx F).jL i t g) = 0 := hg
    rw [← hw, LinearMap.adjoint_inner_left, h4, inner_zero_right]
  have h5 : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jV i t f) (R.jV i t g)) = 0 := h3
  rw [inner_jV h1 h2, map_eq_zero, map_eq_zero] at h5
  exact h5

def srcF (F : Face D A) (i : Fin D.R.m) (t : T0) : (Fin (OntoChain.srcDim F i t) → D.what₂.LL) →ₗ[D.what₂.LL] A.fam.amb.FL i t :=
  srcForm A i t F.P0 F.ψ0⁻¹

theorem toF_eq_srcF {s : ℕ} (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L i t).dZ (liftLvl F) (liftSub R F i t)) → D.what₂.LL) :
    (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y =
      srcF F i t (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y) := by
  have := BlockDat.lf_lvlE_lE (Z := liftSub R F i t) (blockHyp (F := F) hOk i t)
  show (A.fam.L i t).S.basis.equivFun.symm (((A.fam.L i t).vE (liftLvl F)).mulVec
    (((A.fam.L i t).zE (liftLvl F) (liftSub R F i t)).mulVec y)) = (A.fam.L i t).S.basis.equivFun.symm
    (((A.fam.L i t).S.lvlE (A.fam.L i t).r (liftLvl F).P (liftLvl F).ψ).mulVec
      (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, this]
  rfl

theorem lPr_eq_zero_of_ker {s : ℕ} (hOk : A.fam.Ok s) (hHV : R.models_HV) (hjV : R.models_jV) (i : Fin D.R.m) (t : T0)
    (k : Fin (OntoChain.srcDim F i t) → D.what₂.LL) (hk : R.thG i t (R.jV i t (srcF F i t k)) = 0) :
    ((A.fam.L i t).lPr (liftLvl F) (liftSub R F i t)).mulVec k = 0 := by
  refine lPr_eq_zero (Z := liftSub R F i t) (blockHyp (F := F) hOk i t) k fun y' => ?_
  have hm : (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y' ∈ liftSub R F i t := by
    obtain ⟨f, hf, e⟩ : ((A.fam.L i t).zE (liftLvl F) (liftSub R F i t)).mulVec y' ∈
      (A.fam.L i t).Z0 (liftLvl F) (liftSub R F i t) := (subspace_image_spec _ _ _).2.le ⟨y', rfl⟩
    have : (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y' = f :=
      (congrArg (A.fam.L i t).S.basis.equivFun.symm e.symm).trans ((A.fam.L i t).S.basis.equivFun.symm_apply_apply f)
    exact this ▸ hf
  have := csum_eq_zero hHV hjV i t hm hk
  rw [(A.fam.L i t).S.isClassSum, BlockDat.fE, ← Matrix.mulVec_mulVec]
  exact this

theorem lift_sub (i : Fin D.R.m) (t : T0) (x y : Fin (OntoChain.srcDim F i t) → D.what₂.LL) :
    R.thG i t (R.jV i t (srcF F i t (x - y))) = R.thG i t (R.jV i t (srcF F i t x)) - R.thG i t (R.jV i t (srcF F i t y)) :=
  ((R.thG i t).toAddMonoidHom.comp ((R.jV i t).toAddMonoidHom.comp (srcF F i t).toAddMonoidHom)).map_sub x y

theorem eq_thetaOp {s : ℕ} (hOk : A.fam.Ok s) (hHV : R.models_HV) (hjV : R.models_jV) (hU : R.LUnif) (h5 : R.LTheta F)
    (hr : R.LRatTh F) (i : Fin D.R.m) (t : T0) (x : Fin (OntoChain.srcDim F i t) → D.what₂.LL) {u : Fin (R.nW i) → D.what₂.LL}
    (hu : u ∈ R.WL F false i) (ha : (R.FW i).j (sg0 D A) u = R.thG i t (R.jV i t (srcF F i t x))) :
    u = thetaOp R F i t x := by
  rw [← range_coordMap] at hu
  obtain ⟨z, rfl⟩ := hu
  obtain ⟨y, rfl⟩ : ∃ y, (thetaMat R F i t).mulVec y = z := ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false)
    (RealDat.ewNorm false) (RealDat.nP_pos false) (h5 false) (hr false) i t).2 z
  have hb : _ = R.thG i t (R.jV i t (srcF F i t (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y))) :=
    (j_thetaMat h5 hr i t y).trans (congrArg (fun f => R.thG i t (R.jV i t f)) (toF_eq_srcF hOk i t y))
  have h0 := lPr_eq_zero_of_ker hOk hHV hjV i t (x - ((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y)
    ((lift_sub i t _ _).trans (sub_eq_zero.2 (ha.symm.trans hb)))
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, BlockDat.lf_lPr_lE (blockHyp (F := F) hOk i t), Matrix.one_mulVec,
    sub_eq_zero] at h0
  rw [← h0, Matrix.mulVec_mulVec]
  rfl

theorem goodOp_classSum {s : ℕ} (hOk : A.fam.Ok s) {ph : Fin D.R.m → ℂ} (hG : PhasedLift R ph) (hHV : R.models_HV)
    (hjV : R.models_jV) (hHW : R.models_HW) (hU : R.LUnif) (h5 : R.LTheta F) (hr : R.LRatTh F) (i : Fin D.R.m) (t : T0)
    {θ : (Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : OnTies.IsClassSum R i t F.P0 F.ψ0⁻¹ (ph i) θ) (x : Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL)
    (hx : goodOp R i (θ x) ∈ R.WL F false i) : goodOp R i (θ x) = thetaOp R F i t x := by
  refine eq_thetaOp hOk hHV hjV hU h5 hr i t x hx ((hHW i _).1 ?_)
  refine (adForm_goodOp hU i _).trans ?_
  refine (congrArg (postOn _ (R.eWf i (sg0 D A))) (hθ x)).trans ?_
  exact (LinearMap.map_smul _ _ _).trans (hG i t _).symm

theorem chi_eq_one (h1 : R.grp_levels F) (h2 : R.grp_chiW) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (mem_base_iff h1 g).1 hg
  have hm := (mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  apply Units.ext
  apply D.what₂.embLL.injective
  rw [h2, Units.val_one, map_one, eG_mirIncl]
  refine Finset.prod_eq_one fun PP _ => ?_
  have h3 := hm PP (Set.mem_univ _)
  have : Matrix.GeneralLinearGroup.det (mirToGL R u PP) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (fun a b hab => h3.1 hab)]
    exact Finset.prod_eq_one fun a _ => h3.2 a
  rw [this, map_one, Units.val_one]

end ClassSum

section Chart

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
  {P : Type} [Group P] [Finite P] {c : OnConst}

abbrev withCoord (O : OnObj ((R.toCx F).data F.cr false) P c)
    (w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL)) :
    OnObj ((R.toCx F).data F.cr false) P c :=
  { O with φ := fun j => (w j).symm.toLinearMap ∘ₗ coordMap R F j }

variable {O : OnObj ((R.toCx F).data F.cr false) P c}
  {w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL)} {inc : P →* G}

theorem mem_Zg_iff (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hinc : F.P0 ≤ inc.range) (j : Fin D.R.m)
    (hρ : ∀ g x, w j (O.ρ j g x) = (R.FW j).ρ (inc g) (w j x)) (hU : O.U = F.P0.comap inc)
    (hψ : ∀ (g : P) (hg : inc g ∈ F.P0), ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) = (F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ))
    (he : ∀ x, w j (O.e j x) = goodOp R j (w j x)) (hV : O.V₀ j = LinearMap.range (O.e j))
    (x : Fin (O.nZ j) → D.what₂.LL) : x ∈ O.Zg j ↔ w j x ∈ R.WL F false j := by
  have e1 : x ∈ eig (O.ρ j) O.U O.ψ ↔ ∀ u : O.U, O.ρ j u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ j g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW j).ρ (inc g) (w j x) = (((R.FW j).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • w j x :=
    fun g hg => by
      rw [chi_eq_one h1 h2 j hg, one_mul, ← hψ g hg, ← hρ, ← LinearEquiv.map_smul, (w j).injective.eq_iff]
  refine and_congr (e1.trans ⟨?_, fun h u => ?_⟩) ⟨?_, ?_⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨p, rfl⟩ := hinc hg
    exact (e2 p hg).1 (h ⟨p, hU ▸ hg⟩)
  · have hg : inc u ∈ F.P0 := (hU ▸ u.2 : (u : P) ∈ F.P0.comap inc)
    exact (e2 u hg).2 (h ⟨inc u, hg⟩)
  · intro hx
    obtain ⟨y, rfl⟩ : x ∈ LinearMap.range (O.e j) := hV ▸ hx
    exact ⟨w j y, (he y).symm⟩
  · rintro ⟨y, hy⟩
    have : x ∈ LinearMap.range (O.e j) := ⟨(w j).symm y, (w j).injective (by
      rw [he, LinearEquiv.apply_symm_apply]; exact hy)⟩
    exact hV ▸ this

theorem coord_lattice (j : Fin D.R.m) (hZ : ∀ x, x ∈ O.Zg j ↔ w j x ∈ R.WL F false j)
    (hM : ∀ x, x ∈ O.Ms j ↔ w j x ∈ supLat (R.FW j)) :
    Function.Injective ((withCoord O w).φ j) ∧ LinearMap.range ((withCoord O w).φ j) = O.Zg j ∧
      (((R.toCx F).data F.cr false).M j).map (((withCoord O w).φ j).restrictScalars (𝓞 D.what₂.LL)) =
        cut (O.Zg j) (O.Ms j) := by
  have hφ : ∀ z, w j ((withCoord O w).φ j z) = coordMap R F j z := fun z => (w j).apply_symm_apply _
  have hsur : ∀ x, w j x ∈ R.WL F false j → ∃ z, (withCoord O w).φ j z = x := fun x hx => by
    rw [← range_coordMap] at hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, (w j).injective ((hφ z).trans hz)⟩
  have hmem : ∀ z, coordMap R F j z ∈ R.WL F false j := fun z => (range_coordMap j).le ⟨z, rfl⟩
  have hMz : ∀ z, z ∈ ((R.toCx F).data F.cr false).M j ↔ coordMap R F j z ∈ supLat (R.FW j) := fun z =>
    ⟨fun h => h.1.1, fun h => ⟨⟨h, (hmem z).1⟩, (hmem z).2⟩⟩
  refine ⟨(w j).symm.injective.comp (coordMap_injective j), le_antisymm ?_ fun x hx => hsur x ((hZ x).1 hx),
    le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact (hZ _).2 (hφ z ▸ hmem z)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(hM _).2 (hφ z ▸ (hMz z).1 hz), (hZ _).2 (hφ z ▸ hmem z)⟩
  · rintro x ⟨h1, h2⟩
    obtain ⟨z, rfl⟩ := hsur x ((hZ x).1 h2)
    exact ⟨z, (hMz z).2 (hφ z ▸ (hM _).1 h1), rfl⟩

theorem coord_tuple (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (y : (Fin (O.nX v j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OntoChain.srcDim F j (R.mu v)) → D.what₂.LL))
    (hMt : ∀ x, x ∈ O.Mt v j ↔ y x ∈ srcLat F j (R.mu v))
    (hθ : ∀ x ∈ O.Mt v j, w j (O.e j (O.θ' v j x)) = thetaOp R F j (R.mu v) (y x))
    (hI : O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
      ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)) :
    (withCoord O w).TjId j v (R.mu v) := by
  have h3 : ∀ x, O.θ' v j (O.pr v j (O.eX v j x)) = O.e j (O.θ' v j x) := fun x => by
    have := hI.2 _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.map_sub, sub_eq_zero] at this
    exact this.symm.trans (LinearMap.congr_fun hI.1 x)
  have h4 : ∀ x ∈ O.Mt v j, (withCoord O w).φ j ((thetaMat R F j (R.mu v)).mulVec
      (((A.fam.L j (R.mu v)).lPr (liftLvl F) (liftSub R F j (R.mu v))).mulVec (y x))) =
        O.θ' v j (O.pr v j (O.eX v j x)) := fun x hx => by
    rw [h3, Matrix.mulVec_mulVec]
    exact (w j).symm_apply_eq.2 (hθ x hx).symm
  apply le_antisymm
  · rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨x, rfl⟩ := y.surjective x
    exact ⟨_, ⟨_, ⟨x, (hMt x).2 hx, rfl⟩, rfl⟩, (h4 x ((hMt x).2 hx)).symm⟩
  · rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y x, (hMt x).1 hx, rfl⟩, rfl⟩, h4 x hx⟩

end Chart

section Tied

open Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.OnTies GlobalTheory.FormTies
open scoped TensorProduct

structure RunData (J : CoreJ D) : Type 1 where
  G : In66 J.Q
  nab : ∀ j, NabV (J.Q.Xo j) J.Q.c
  dδ : ∀ j n, DeltaDat (J.Q.Xo j) J.Q.c n
  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  half₂ : Ideal (𝓞 D.host.E)

def RunData.full {J : CoreJ D} (r : RunData J) : Full D :=
  { toCore := J.toCore, G := r.G, nab := r.nab, dδ := r.dδ, cE := J.cE, chiW := J.chiW, x₀ := J.x₀, iota := J.iota,
    xi := r.xi, half₂ := r.half₂ }

def RunData.of (T : Full D) : RunData T.J := ⟨T.G, T.nab, T.dδ, T.xi, T.half₂⟩

theorem RunData.full_of (T : Full D) : (RunData.of T).full = T := rfl

theorem RunData.full_J {J : CoreJ D} (r : RunData J) : r.full.J = J := rfl

theorem map_spanK (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {m n : ℕ}
    (f : B.Cusp j w →ₗ[B.KO] (Fin m → K)) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) (t : Set (Fin m → K))
    (h1 : ∀ x, f x ∈ t ↔ x ∈ B.Mlat j w) (h2 : ∀ u ∈ t, u ∈ LinearMap.range f) :
    (spanK z (B.Mlat j w : Set _)).map ((f.liftBaseChange K ∘ₗ z.toLinearMap).restrictScalars (𝓞 K)) =
      Submodule.span (𝓞 K) t := by
  have e : ∀ x, (f.liftBaseChange K ∘ₗ z.toLinearMap) (z.symm (1 ⊗ₜ x)) = f x := fun x => by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.liftBaseChange_tmul, one_smul]
  unfold spanK
  rw [Submodule.map_span]
  congr 1
  ext u
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (e x).symm ▸ (h1 x).2 hx
  · intro hu
    obtain ⟨x, rfl⟩ := h2 u hu
    exact ⟨_, ⟨x, (h1 x).1 hu, rfl⟩, e x⟩

section One

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem mem_Ms_iff (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (x : Fin (O.nZ i) → D.what₂.LL) :
    x ∈ O.Ms i ↔ toForms h fw ι z x ∈ supLat (R.FW ι) := by
  have e : (O.Ms i).map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) = supLat (R.FW ι) :=
    (congrArg _ t.Ms_eq).trans (map_spanK (recB h.toLawsCore) (cuspTo h fw ι) z _
      (fun f => (fw.mem_MK ι ⟨f.1, cutR_le _ _ _ f.2⟩).trans ⟨fun H la v hv => H la ⟨v, hv⟩, fun H la y => H la y.1 y.2⟩)
      fun u hu => (cutTo_spec fw ι).2.ge ((R.FW ι).MK_le_WK hu))
  rw [← e]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨x', hx', e'⟩ => (toForms_bijective h fw ι z).1 e' ▸ hx'⟩

end One

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

def OnObjLevelCompatibility (F : Face D A) (fw : FWTie J R κ v₀) (hc : LawsCore J.toCore) (run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J)
    (h : ∀ v, LawsP (run v).full.toTop) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
    (wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (nT : ℕ)
    (ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l))
    (ph : Fin D.R.m → ℂ) {P : Type} [Group P] [Finite P] (inc : P →* G) {c : OnConst}
    (O : OnObj ((R.toCx F).data F.cr false) P c) : Prop :=
  ∃ (z : ∀ i : Fin D.R.m, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB hc).KO] (recB hc).Cusp ((i : ℕ) + 1) (κ i))
    (act : ∀ i : Fin D.R.m, P → (recB hc).Cusp ((i : ℕ) + 1) (κ i) → (recB hc).Cusp ((i : ℕ) + 1) (κ i))
    (y : ∀ v (i : Fin D.R.m), (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      (Fin (OnTies.srcDim A i (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)),
    ∀ v (i : Fin D.R.m), OnTie (T := (run v).full) (R := R) (h v) fw hinj EX (p v) i (wL v i) (wF v i) nT O v i
        (z i) (act i) inc (ℓ i) F.P0 F.ψ0⁻¹ (ph i) (y v i) ∧
      ActionPin (T := (run v).full) (R := R) (h v) fw i (ℓ i)

variable (R F) in

def TwistedRational (ph : Fin D.R.m → ℂ) : Prop :=
  ∀ w ∈ R.twPl, ∀ i, ClassSumRational R i (R.mu w) F.P0 F.ψ0⁻¹ (ph i)

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst} {s : ℕ}

theorem exists_tieCoord {P : Type} [Group P] [Finite P] {inc : P →* G} {O : OnObj ((R.toCx F).data F.cr false) P c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph inc O) (hinc : F.P0 ≤ inc.range)
    (hOk : A.fam.Ok s) (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hHV : R.models_HV) (hjV : R.models_jV) (hHW : R.models_HW)
    (hμ : R.tup_mu_conj) (hG : PhasedLift R ph) (hU : R.LUnif) (h5 : R.LTheta F) (hr : R.LRatTh F)
    (hrat : TwistedRational R F ph) (hI : LeafIdentity O) (hT : LeafTW2 O) : ∃ w, TieCoord (withCoord O w) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  let w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) := fun j =>
    LinearEquiv.ofBijective (toForms (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
      (toForms_bijective (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
  have he : ∀ j x, w j (O.e j x) = goodOp R j (w j x) := fun j x => (ht v₁ j).1.e_eOp x
  have hZ : ∀ j x, x ∈ O.Zg j ↔ w j x ∈ R.WL F false j := fun j =>
    mem_Zg_iff h1 h2 hinc j ((ht v₁ j).1.rho_eq_of_actionPin (ht v₁ j).2) (ht v₁ j).1.U_eq (ht v₁ j).1.ψ_eq (he j)
      (ht v₁ j).1.V₀_eq
  have hM : ∀ j x, x ∈ O.Ms j ↔ w j x ∈ supLat (R.FW j) := fun j x => mem_Ms_iff (ht v₁ j).1 x
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j) →
      (O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)) →
      IsLatIn (O.Zg j) (O.Im v j) → (withCoord O w).TjId j v (R.mu v) := fun v j hra hI hT => by
    refine coord_tuple j v (y v j) (fun x => by rw [(ht v j).1.Mt_eq]; rfl) (fun x hx => ?_) hI
    have hθ : OnTies.IsClassSum R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j)
        ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) := (ht v j).1.θ'_eq hra
    have e : ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) (y v j x) = w j (O.θ' v j x) :=
      congrArg (fun u => w j (O.θ' v j u)) ((y v j).symm_apply_apply x)
    have hm : w j (O.e j (O.θ' v j x)) ∈ R.WL F false j :=
      (hZ j _).1 (hT.2.le (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩))
    have := goodOp_classSum hOk hG hHV hjV hHW hU h5 hr j (R.mu v) hθ (y v j x) (by rw [e, ← he]; exact hm)
    rw [e, ← he] at this
    exact this
  refine ⟨w, fun j => coord_lattice j (hZ j) (hM j), fun v hv j =>
    ⟨key v j (hrat v hv j) ((hI v hv).1 j) ((hT v hv).1 j).2.1, ?_⟩⟩
  have := key (conjPl v) j (by rw [hμ v]; exact hrat v hv j) ((hI v hv).2 j) ((hT v hv).2 j).2.1
  rwa [hμ v] at this

theorem level_of_tied {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph (mirIncl R) O) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    (h1 : R.grp_levels F) : (TieU O fun v => uniSub (Res R v) (rankPred D.R)) ∧ LeafMackey O ∧ LeafProj O := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v, -⟩ := exists_place3 D.what₂.LL
  have t := (ht v ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩).1
  have hU : O.U = uni R := t.U_eq.trans (Subgroup.ext fun g => (mem_base_iff h1 _).trans
    ⟨fun ⟨u, hu, e⟩ => mirIncl_injective R e ▸ hu, fun hg => ⟨g, hg, rfl⟩⟩)
  have hψ : ∀ u ∈ uni R, O.ψ u = psiU (Res R) (rankPred D.R) (levelChar R F) _ u := fun u hu =>
    have hm := (mem_base_iff h1 _).2 ⟨u, hu, rfl⟩
    Subtype.ext ((t.ψ_eq u hm).trans ((levelChar_spec h1).val u hu hm).symm)
  obtain ⟨m1, m2, m3⟩ : IsMackey (uni R) (psiU (Res R) (rankPred D.R) (levelChar R F) _) :=
    leafMackey (F := F) c (supArgs R) h1
  refine ⟨hU, ?_, fun j => ⟨LinearMap.ext fun x => ?_, (ht v j).1.V₀_eq.symm⟩⟩
  · unfold LeafMackey
    rw [hU]
    refine ⟨(hψ 1 (one_mem _)).trans m1, fun u hu u' hu' => ?_, fun g hg => ?_⟩
    · rw [hψ _ (mul_mem hu hu'), hψ u hu, hψ u' hu', m2 u hu u' hu']
    · obtain ⟨u, hu, hu', hne⟩ := m3 g hg
      exact ⟨u, hu, hu', by rwa [hψ _ hu', hψ u hu]⟩
  · refine (toForms_bijective (T := (run v).full) (R := R) (h v) fw j (z j)).1 ?_
    refine ((ht v j).1.e_eOp _).trans ((congrArg (goodOp R j) ((ht v j).1.e_eOp x)).trans ?_)
    exact (LinearMap.congr_fun (goodOp_idem hX j) _).trans ((ht v j).1.e_eOp x).symm

theorem onto_of_tied_phase {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c} (C CH : ℝ)
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph (mirIncl R) O)
    (hOk : A.fam.Ok s) (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hHV : R.models_HV) (hjV : R.models_jV) (hHW : R.models_HW)
    (hμ : R.tup_mu_conj) (hG : PhasedLift R ph) (hU : R.LUnif) (h5 : R.LTheta F) (hr : R.LRatTh F)
    (hrat : TwistedRational R F ph) (hRk : RankRows ((R.toCx F).data F.cr false))
    (hN : TieLevelNum O (rankPred D.R) D.R.f) (hSq : LeafLevelSq O (Res R) D.R.f) (hY : LeafYBound O)
    (hSup : LeafSup O) (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (hT2 : LeafTW2 O) (hT1 : LeafTW1 O) (hSh : LeafShareI O) (hBS : LeafBadShare O)
    (hDG : LeafDepthGood (R.num F C CH) O) (hDR : LeafDepthRam (R.num F C CH) O) (hD2 : LeafDepth2 (R.num F C CH) O)
    (hDL : LeafDepthLevel (R.num F C CH) O) (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (R.num F C CH) O) (hCE : c.CE ≤ C) (tE1 : ErrorConstantMatchesDefinition (R.num F C CH) O C) :
    (withErr R O.errOn).LOnto F C CH ∧ (TieErr O → R.LOnto F C CH) := by
  classical
  obtain ⟨w, hw⟩ := exists_tieCoord ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hHV hjV hHW hμ hG hU h5 hr hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact onto_of_coord (withCoord O w) C CH hRk hw hMk hSup hP hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hJS hJE hCE tE1

theorem onto_of_tied {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c} (C CH : ℝ)
    (hC : R.Char F) (hOk : A.fam.Ok s)
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ (fun _ => 1) (mirIncl R) O)
    (hU : R.LUnif) (h5 : R.LTheta F) (hr : R.LRatTh F) (hrat : TwistedRational R F fun _ => 1)
    (hRk : RankRows ((R.toCx F).data F.cr false))
    (hN : TieLevelNum O (rankPred D.R) D.R.f) (hSq : LeafLevelSq O (Res R) D.R.f) (hY : LeafYBound O)
    (hSup : LeafSup O) (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (hT2 : LeafTW2 O) (hT1 : LeafTW1 O) (hSh : LeafShareI O) (hBS : LeafBadShare O)
    (hDG : LeafDepthGood (R.num F C CH) O) (hDR : LeafDepthRam (R.num F C CH) O) (hD2 : LeafDepth2 (R.num F C CH) O)
    (hDL : LeafDepthLevel (R.num F C CH) O) (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (R.num F C CH) O) (hCE : c.CE ≤ C) (tE1 : ErrorConstantMatchesDefinition (R.num F C CH) O C) :
    ((withErr R O.errOn).Char F ∧ (withErr R O.errOn).LOnto F C CH) ∧ (TieErr O → R.LOnto F C CH) :=
  have k := onto_of_tied_phase C CH ht hOk hC.grp.levels hC.grp.chiW hC.models.HV hC.models.jV hC.models.HW hC.tup.mu_conj
    (phasedLift_one hC.thP.thG) hU h5 hr hrat hRk hN hSq hY hSup hSp hS hT0 hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX
    hBad hJS hJE hCE tE1
  ⟨⟨char_withErr hC _, k.1⟩, k.2⟩

def scaledSpan {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (nT : ℕ) {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) : Submodule (𝓞 K) (Fin n → K) :=
  spanK z {f | X.inc ka f ∈ X.Theta (scalOfP B hinj EX p ka wL wF nT) ka wL wF nT}

def shortSpan {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (ka : WeightFamilies.Wt D j)
    {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) : Submodule (𝓞 K) (Fin n → K) :=
  spanK z (X.shortTh ka : Set _)

def runScalar (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ} (ka wL wF : WeightFamilies.Wt D j)
    (nT : ℕ) (K : Type) [Field K] [Algebra B.KO K] : K :=
  algebraMap B.KO K (sigRec B hinj EX ka wL wF nT : 𝓞 B.KO)

theorem exists_tiedObj {P : Type} [Group P] [Finite P] (inc : P →* G) (O : OnObj ((R.toCx F).data F.cr false) P c)
    (ha : ∀ v (i : Fin D.R.m), ActionPin (T := (run v).full) (R := R) (h v) fw i (ℓ i))
    (ρ : ∀ i : Fin D.R.m, Representation (recB hc).KO P ((recB hc).Cusp ((i : ℕ) + 1) (κ i)))
    (hρ : ∀ v (i : Fin D.R.m), IsLevAct (run v).full.toTop (h v) ((i : ℕ) + 1) (κ i) (fun g => ℓ i (inc g)) fun g f => ρ i g f) :
    ∃ O' : OnObj ((R.toCx F).data F.cr false) P c, OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph inc O' := by
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  obtain ⟨O₁, z, y, -, H⟩ := exists_onTie (T := (run v₁).full) (R := R) (h v₁) fw hinj EX O (fun i => i) p (wL v₁) (wF v₁) nT
    inc ℓ ρ (hρ v₁) F.P0 F.ψ0⁻¹ ph
  let O' : OnObj ((R.toCx F).data F.cr false) P c :=
    { O₁ with
      Th := fun v i => scaledSpan (recPJ (h v) ((i : ℕ) + 1) (inR_succ i)) hinj EX (p v) (κ i) (wL v i) (wF v i) nT (z i)
      σ := fun v i => runScalar (recB (h v).toLawsCore) hinj EX (κ i) (wL v i) (wF v i) nT D.what₂.LL
      ThK := fun v i => shortSpan (recPJ (h v) ((i : ℕ) + 1) (inR_succ i)) (κ i) (z i)
      Th0 := fun v i => thetaEig (h v) ((i : ℕ) + 1) (κ i) (z i) O₁.U O₁.ψ fun g => ℓ i (inc g) }
  exact ⟨O', z, fun i g f => ρ i g f, y, fun v i =>
    ⟨{ Ms_eq := (H v i).Ms_eq, rho_eq := (H v i).rho_eq, Th_eq := rfl, σ_eq := rfl, ThK_eq := rfl, act_eq := hρ v i,
       U_eq := (H v i).U_eq, ψ_eq := (H v i).ψ_eq, e_eq := (H v i).e_eq, V₀_eq := (H v i).V₀_eq, Th0_eq := rfl,
       ThJ_eq := (H v i).ThJ_eq, X₃_eq := (H v i).X₃_eq, Mt_eq := (H v i).Mt_eq, θ'_eq := (H v i).θ'_eq,
       eX_eq := (H v i).eX_eq, pr_eq := (H v i).pr_eq }, ha v i⟩⟩

end Tied

end GlobalTheory.RealIndexBound
