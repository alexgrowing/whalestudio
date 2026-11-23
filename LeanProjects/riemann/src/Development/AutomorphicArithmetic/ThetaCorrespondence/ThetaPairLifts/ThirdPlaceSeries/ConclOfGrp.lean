import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueOfRayClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRowTame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSideStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.TopA
def ConclAlt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Prop :=
  ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_au_true_and_types_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (h1 : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT))
    (h2 : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au) (h3 : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR)
    (h4 : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W)
    (h5 : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (h6 : LabConj D A.wdT) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep :=
  ⟨lay0 D, ⟨D.Z_tie, D.Zgood_tie⟩, D.etaJ_tie, A, h1, h2, h3, h4, rfl, HEq.rfl, HEq.rfl, HEq.rfl, h5, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, h6⟩
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem concl_setK_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk)
    (k1 : L.nd.PlG = D.nd.PlG) (k2 : HEq L.naut.plGw D.naut.plGw) (k3 : HEq L.ntypes.cenAmb D.ntypes.cenAmb)
    (k4 : HEq L.ntypes.cenMt D.ntypes.cenMt) (k5 : L.loc = D.loc) (k6 : HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd))
    (k7 : HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd))
    (k8 : HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd))
    (k9 : HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd))
    (h : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setK D L hZ hη) (cfK L hZ hη cf) jE rep) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨L', hZ', hη', A, h1, h2, h3, h4, e1, e2, e3, e4, h5, e5, e6, e7, e8, e9, h6⟩ := h
  exact ⟨L', hZ', hη', A, h1, h2, h3, h4, e1.trans k1, e2.trans k2, e3.trans k3, e4.trans k4, h5, e5.trans k5, e6.trans k6,
    e7.trans k7, e8.trans k8, e9.trans k9, h6⟩
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_automorphic_side_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T)) (chr : CharSide D cf) (au : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (hau : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T au) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨Pl⟩ := GlobalTheory.HeightCounting.nonempty_plSide D
  obtain ⟨X, h1, h0, e1, e2, e3, e4, e5, ⟨par⟩, hι⟩ := GlobalTheory.ParRay.exists_types hR hC D hE jE Pl hray
  obtain ⟨Γ', hΓ⟩ := exists_grp_setTy D hE X h1 h0 e1 e2 e3 Γ
  obtain ⟨wd⟩ := GlobalTheory.HeightCounting.exists_wdSide hdR (setTy D hE X h1 h0) T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setTy D hE X h1 h0) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlab' : LabTrue (setTy D hE X h1 h0) T := by
    intro k v a
    have := hlab k v a
    rw [← e1, ← e2] at this
    exact this
  have hconj' : LabConj (setTy D hE X h1 h0) T := by
    intro k v w hw
    have := hconj k v w hw
    rw [← e1, ← e2] at this
    exact this
  have hχ' : ChiTOk (setTy D hE X h1 h0) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← e1, ← e2] at this
    exact this
  have hT' : GlobalTheory.Mem.Top.TypesTrue X cf.P cf.W :=
    ⟨hT.pl, fun k => (congrFun e2 k).trans (hT.teich k), hT.chi, fun k p => (congrFun (congrFun e3 k) p).trans (hT.ser k p)⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setTy D hE X h1 h0) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_au_true_and_types_true hL (setTy D hE X h1 h0) cf' jE rep
      { bare := hE, wdT := T, lab := hlab', chr := { chr with }, row := ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩
        pl := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩, iota := hι ⟨Γ⟩, wd := wd, grp := Γ', par := par, au := { au with }
        chiT := hχ' }
      ⟨{ cg with }⟩ hau hrow hT' (fun k => (congrFun hΓ k).trans (hζ k)) hconj'
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setTy D hE X h1 h0)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl (heq_of_eq e4) (heq_of_eq e5) rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_cusp_galois_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T)) (chr : CharSide D cf) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨C, au, hau⟩ := _root_.GlobalTheory.T.exists_nbc_auSide_true_of_isEmpty_loc hL D hE T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setBC D C) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setBC D C) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_automorphic_side_true hL hdR hR hC (setBC D C) hE cf' jE rep hray hT { Γ with } hζ hχ T hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow
      ⟨{ cg with }⟩ { chr with } au hau
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setBC D C)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_local_parameters_true (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR) :
    _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨K, hcg, ⟨chr⟩⟩ := _root_.UpperTheory.One.M.New.exists_cgTrue_charSide hL hA D hE T cf hT.pl
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setCG D hE K) (cfCG hE K cf) jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_cusp_galois_true hL hdR hR hC (setCG D hE K) hE (cfCG hE K cf) jE rep hray ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩ { Γ with } hζ hχ
      (wdCG hE K T) hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow hcg chr
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setCG D hE K)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem conclusion_of_group_side (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (hd : RowDepth D rep) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨Rw, hRw⟩ := _root_.GlobalTheory.RowPar.exists_rowWD_rowTrue_m_alt hL D rep hd
  obtain ⟨lab, h, A, C, tm, tg, hl, hpl, T, hlab, hconj, Rs, hp, hs⟩ := GlobalTheory.HeightCounting.exists_setAut_wdTie_labConj D hE Rw
  let cf' : CharFrame (setAut D hE lab h A C tm tg hl) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hk := fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_kv_of_eq D (hpl k v) (D.ntypes.tg k v) (Γ.ζ k) (Γ.kv k v) (Γ.tg_tame k v)
  choose kv hkv using hk
  have hχ' : ChiTOk (setAut D hE lab h A C tm tg hl) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← hpl k v] at this
    exact this
  have hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setAut D hE lab h A C tm tg hl) rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR := by
    have e1 : (fun σ w => T.e w (Rs.locR σ w)) = Rw.par := funext fun σ => funext fun w => hp σ w
    have e2 : Rs.satR = Rw.sat := funext fun σ => funext fun w => hs σ w
    rw [e1, e2]
    exact hRw
  have hT' : GlobalTheory.Mem.Top.TypesTrue (setAut D hE lab h A C tm tg hl).ntypes cf.P cf.W :=
    ⟨fun k v => (hpl k v).symm ▸ hT.pl k v, hT.teich, hT.chi, hT.ser⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setAut D hE lab h A C tm tg hl) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_local_parameters_true hA hL hdR hR hC (setAut D hE lab h A C tm tg hl) hE cf' jE rep hray hT'
      { Γ with kv := kv, tg_tame := hkv } hζ hχ' T hlab hconj Rs hrow
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setAut D hE lab h A C tm tg hl)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl (heq_of_eq (funext fun k => funext fun v => hpl k v)) HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_sideA_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → RowDepth D rep → (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT := by
  intro hL hA hdR hG hAr hR hC D hE cf jE rep hz hT hd hray
  obtain ⟨L, hZ, hη, hE', hT', k1, k2, k3, k4, ⟨Γ, hζ⟩, hχ, k5, k6, k7, k8, k9⟩ := GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling hG hAr D hE cf hz hT
  have hd' : RowDepth (setK D L hZ hη) rep := by
    intro σ k v
    obtain ⟨v₀, e⟩ := exists_eq_of_heq k1 k2 k v
    obtain ⟨s, τ, h1, h2⟩ := hd σ k v₀
    exact ⟨s, τ, h1.trans e, h2⟩
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep L hZ hη k1 k2 k3 k4 k5 k6 k7 k8 k9
    (_root_.GlobalTheory.HeightCounting.TopA.conclusion_of_group_side hA hL hdR hR hC (setK D L hZ hη) hE' (cfK L hZ hη cf) jE rep hray hT' Γ hζ hχ hd')
end GlobalTheory.HeightCounting.TopA
end
end
