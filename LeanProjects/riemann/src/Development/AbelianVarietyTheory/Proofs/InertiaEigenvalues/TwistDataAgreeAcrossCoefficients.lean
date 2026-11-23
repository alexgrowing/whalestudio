import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

structure SameGalois {D D' : D7} (N : NData D.R D.host D.what₂) (N' : NData D'.R D'.host D'.what₂) : Prop where
  R : D.R = D'.R
  host : HEq D.host D'.host
  loc : D.loc = D'.loc
  Om : HEq (@NData.Om _ _ _ N) (@NData.Om _ _ _ N')
  instOm : HEq (@NData.instOm _ _ _ N) (@NData.instOm _ _ _ N')
  algOm : HEq (@NData.algOm _ _ _ N) (@NData.algOm _ _ _ N')
  plOm : HEq (@NData.plOm _ _ _ N) (@NData.plOm _ _ _ N')
  PlG : HEq (@NData.PlG _ _ _ N) (@NData.PlG _ _ _ N')

structure TwistDataAgreeAcrossCoefficients {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    (X : NTw D.R D.host D.what₂ D.LL0 N) (X' : NTw D'.R D'.host D'.what₂ D'.LL0 N') : Prop where
  cc : HEq X.cc X'.cc
  Tw : HEq X.Tw X'.Tw
  l : HEq X.l X'.l
  O0 : HEq X.O0 X'.O0
  crO0 : HEq X.crO0 X'.crO0
  algO0 : HEq X.algO0 X'.algO0
  topO0 : HEq X.topO0 X'.topO0
  O : HEq X.O X'.O
  crO : HEq X.crO X'.crO
  algO : HEq X.algO X'.algO
  Ok : HEq X.Ok X'.Ok
  crOk : HEq X.crOk X'.crOk
  algOk : HEq X.algOk X'.algOk
  zk : HEq X.zk X'.zk
  pD : HEq X.pD X'.pD
  chi1 : HEq X.chi1 X'.chi1
  Sig : HEq X.Sig X'.Sig
  finSig : HEq X.finSig X'.finSig
  jS : HEq X.jS X'.jS
  side : HEq X.side X'.side
  rhoS : HEq X.rhoS X'.rhoS
  S0 : HEq X.S0 X'.S0
  hEig : HEq X.hEig X'.hEig
  abelian₂ : HEq X.abelian₂ X'.abelian₂
  sideL : HEq X.sideL X'.sideL
  RCG : HEq X.RCG X'.RCG
  grpRCG : HEq X.grpRCG X'.grpRCG
  finRCG : HEq X.finRCG X'.finRCG
  art : HEq X.art X'.art
  th : HEq X.th X'.th

structure SameForms {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X') : Prop where
  Fm : HEq Y.Fm Y'.Fm
  acgFm : HEq Y.acgFm Y'.acgFm
  modFmK : HEq Y.modFmK Y'.modFmK
  modFmO : HEq Y.modFmO Y'.modFmO
  actG : HEq Y.actG Y'.actG
  U : HEq Y.U Y'.U
  psiU : HEq Y.psiU Y'.psiU
  eAlg : HEq Y.eAlg Y'.eAlg
  Dat : HEq Y.Dat Y'.Dat
  th : HEq Y.th Y'.th
  lev : HEq Y.lev Y'.lev
  thPsi : HEq Y.thPsi Y'.thPsi
  MtV : HEq Y.MtV Y'.MtV
  acgMt : HEq Y.acgMt Y'.acgMt
  modMtK : HEq Y.modMtK Y'.modMtK
  modMtO : HEq Y.modMtO Y'.modMtO
  MtLat : HEq Y.MtLat Y'.MtLat
  thP : HEq Y.thP Y'.thP
  hkF : HEq Y.hkF Y'.hkF

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem goodTw_transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y')
    {B : BlochKatoReduction.Gen.BKPh X} {B' : BlochKatoReduction.Gen.BKPh X'} (hB : HEq B.br B'.br) (hY : B.ex = Y) (hY' : B'.ex = Y')
    {E : IntegralHeckeForms.ExpDat Y} {E' : IntegralHeckeForms.ExpDat Y'} (hE : HEq E.Dat0 E'.Dat0) {N0 : X.Tw → ℕ} {N0' : X'.Tw → ℕ} (hN : HEq N0 N0')
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') (e : ℝ)
    {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)} {S' : ∀ (j : ℕ) (b : Bool), Finset (Y'.Dat i' j b)} (hS : HEq S S')
    {A Q : Finset (PlE D.host)} {A' Q' : Finset (PlE D'.host)} (hA : HEq A A') (hQ : HEq Q Q') (k : ℕ)
    {ψ : X.RCG i Q →* (X.Ok i k)ˣ} {ψ' : X'.RCG i' Q' →* (X'.Ok i' k)ˣ} (hψ : HEq ψ ψ')
    (h : IntegralHeckeForms.GoodTw Y B E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw Y' B' E' N0' i' e S' A' Q' k ψ' := by
  obtain ⟨br, Y₁⟩ := B
  obtain ⟨br', Y₁'⟩ := B'
  obtain ⟨E, hE₁⟩ := E
  obtain ⟨E', hE₁'⟩ := E'
  dsimp only at hB hY hY' hE
  subst Y₁; subst Y₁'
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hB; subst hE; subst hN; subst hi; subst hS; subst hA; subst hQ; subst hψ
  delta IntegralHeckeForms.GoodTw IntegralHeckeForms.eG IntegralHeckeForms.eO IntegralHeckeForms.Fm0 IntegralHeckeForms.V0 IntegralHeckeForms.Th IntegralHeckeForms.ThPsi
    IntegralHeckeForms.eTh IntegralHeckeForms.eThPsi IntegralHeckeForms.eThPMt IntegralHeckeForms.levs IntegralHeckeForms.SgJ IntegralHeckeForms.IdxAt IntegralHeckeForms.InclAt
    BlochKatoReduction.Gen.GE BlochKatoReduction.Gen.phiK BlochKatoReduction.Gen.chiS BlochKatoReduction.Gen.goodE BlochKatoReduction.Gen.goodS BlochKatoReduction.Gen.SigG
    BlochKatoReduction.Gen.Trep BlochKatoReduction.Gen.Tgl BlochKatoReduction.Gen.DecV BlochKatoReduction.Gen.PDv BlochKatoReduction.Gen.repV BlochKatoReduction.Gen.IsFrac BlochKatoReduction.Gen.IsImgK
    BlochKatoReduction.Gen.bk BlochKatoReduction.Gen.Spl BlochKatoReduction.Gen.selT BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.kMap BlochKatoReduction.Gen.thEval BlochKatoReduction.Gen.c0
    BlochKatoReduction.Gen.tameVal BlochKatoReduction.Gen.TrivAbove BlochKatoReduction.Gen.PsiOk BlochKatoReduction.Gen.partAT BlochKatoReduction.Gen.nu BlochKatoReduction.Gen.partC BlochKatoReduction.Gen.partD at h ⊢
  dsimp only at h ⊢
  exact h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem fullRk_basisOf_transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y')
    {E : IntegralHeckeForms.ExpDat Y} {E' : IntegralHeckeForms.ExpDat Y'} (hE : HEq E.Dat0 E'.Dat0)
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') (j : ℕ) (b : Bool)
    {S : Finset (Y.Dat i j b)} {S' : Finset (Y'.Dat i' j b)} (hS : HEq S S')
    (h : IntegralHeckeForms.FullRk Y E i j b (IntegralHeckeForms.SgJ Y E i j b) ∧ IntegralHeckeForms.BasisOf Y i j b (IntegralHeckeForms.SgJ Y E i j b) S) :
    IntegralHeckeForms.FullRk Y' E' i' j b (IntegralHeckeForms.SgJ Y' E' i' j b) ∧ IntegralHeckeForms.BasisOf Y' i' j b (IntegralHeckeForms.SgJ Y' E' i' j b) S' := by
  delta IntegralHeckeForms.FullRk IntegralHeckeForms.BasisOf IntegralHeckeForms.AO at h ⊢
  rw [N.restN_card_levelGroup_eq] at h
  rw [N'.restN_card_levelGroup_eq]
  obtain ⟨E, hE₁⟩ := E
  obtain ⟨E', hE₁'⟩ := E'
  dsimp only at hE
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hE; subst hi; subst hS
  exact h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem same_basic {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y') :
    X.Tw = X'.Tw ∧
    (Σ (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ), X.RCG i Q →* (X.Ok i k)ˣ) =
      (Σ (i : X'.Tw) (Q : Finset (PlE D'.host)) (k : ℕ), X'.RCG i Q →* (X'.Ok i k)ˣ) ∧
    (∀ i j b, Finset (Y.Dat i j b)) = (∀ i j b, Finset (Y'.Dat i j b)) ∧
    (∀ (p : Σ (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ), X.RCG i Q →* (X.Ok i k)ˣ)
      (p' : Σ (i : X'.Tw) (Q : Finset (PlE D'.host)) (k : ℕ), X'.RCG i Q →* (X'.Ok i k)ˣ), HEq p p' →
      HEq p.1 p'.1 ∧ HEq p.2.1 p'.2.1 ∧ p.2.2.1 = p'.2.2.1 ∧ HEq p.2.2.2 p'.2.2.2) ∧
    ∀ (i : X.Tw) (i' : X'.Tw), HEq i i' → X.l i = X'.l i' ∧
      (∀ (S : ∀ i j b, Finset (Y.Dat i j b)) (S' : ∀ i j b, Finset (Y'.Dat i j b)), HEq S S' →
        HEq (S i) (S' i') ∧ ∀ j b, HEq (S i j b) (S' i' j b)) ∧
      ∀ (a : FractionRing (X.O0 i)) (a' : FractionRing (X'.O0 i')), HEq a a' →
        ((∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = a) ↔
          ∃ y ∈ IsLocalRing.maximalIdeal (X'.O0 i'), algebraMap (X'.O0 i') (FractionRing (X'.O0 i')) y = a') := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  refine ⟨rfl, rfl, rfl, fun p p' hp => ?_, fun i i' hi => ?_⟩
  · subst hp
    exact ⟨HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩
  · subst hi
    refine ⟨rfl, fun S S' hS => ?_, fun a a' ha => ?_⟩
    · subst hS
      exact ⟨HEq.rfl, fun _ _ => HEq.rfl⟩
    · subst ha
      exact Iff.rfl

structure SameExport (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  set : TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  frm : SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  av : avPrimes D = avPrimes D'

theorem SameExport.refl (D : D7) : SameExport D D :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, rfl⟩

theorem SameExport.trans {D D' D'' : D7} (h : SameExport D D') (h' : SameExport D' D'') : SameExport D D'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.frm.Fm.trans h'.frm.Fm, h.frm.acgFm.trans h'.frm.acgFm, h.frm.modFmK.trans h'.frm.modFmK, h.frm.modFmO.trans h'.frm.modFmO, h.frm.actG.trans h'.frm.actG, h.frm.U.trans h'.frm.U, h.frm.psiU.trans h'.frm.psiU, h.frm.eAlg.trans h'.frm.eAlg, h.frm.Dat.trans h'.frm.Dat, h.frm.th.trans h'.frm.th, h.frm.lev.trans h'.frm.lev, h.frm.thPsi.trans h'.frm.thPsi, h.frm.MtV.trans h'.frm.MtV, h.frm.acgMt.trans h'.frm.acgMt, h.frm.modMtK.trans h'.frm.modMtK, h.frm.modMtO.trans h'.frm.modMtO, h.frm.MtLat.trans h'.frm.MtLat, h.frm.thP.trans h'.frm.thP, h.frm.hkF.trans h'.frm.hkF⟩,
    h.br.trans h'.br, h.av.trans h'.av⟩

theorem heq_places {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {A : Finset (PlE H)}
    {A' : Finset (PlE H')} {s : Finset ℕ} (h : ∀ v, v ∈ A ↔ ∃ p ∈ s, v ∈ placesOver H.E p)
    (h' : ∀ v, v ∈ A' ↔ ∃ p ∈ s, v ∈ placesOver H'.E p) : HEq A A' := by
  subst hR
  subst hH
  exact heq_of_eq (Finset.ext fun v => (h v).trans (h' v).symm)

theorem SameExport.avRec {D D' : D7} (h : SameExport D D') : HEq (AvRec D) (AvRec D') :=
  heq_places h.gal.R h.gal.host mem_avRec (by rw [h.av]; exact mem_avRec)

theorem SameExport.good {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    (hg : I.Ok p.1 ∧ IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) (AvRec D) p.2.1 p.2.2.1 p.2.2.2) :
    I'.Ok p'.1 ∧ IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) (AvRec D') p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have hm : D'.R.m = D.R.m := by rw [h.gal.R]
  have h9 := fun j (hj : j ∈ Finset.Icc 1 D'.R.m) b => fullRk_basisOf_transfer h.gal h.set h.frm hE h3 j b ((h8 _ _ hS).2 j b)
    ⟨hg.1.1 j (hm ▸ hj) b, hg.1.2 j (hm ▸ hj) b⟩
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact ⟨⟨fun j hj b => (h9 j hj b).1, fun j hj b => (h9 j hj b).2⟩,
    goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 h.avRec h4 k h6 hg.2⟩

structure SameField (D D' : D7) : Prop where
  LL : D.what₂.LL = D'.what₂.LL
  instLL : HEq D.what₂.instLL D'.what₂.instLL
  places : HEq D.what₂.places D'.what₂.places
  LL0 : HEq D.LL0 D'.LL0
  emb0 : HEq D.ntw.emb0 D'.ntw.emb0
  emb0b : HEq D.ntw.emb0b D'.ntw.emb0b
  tw : ∀ w w', HEq w w' → (TwistedAt D w ↔ TwistedAt D' w')

theorem SameField.refl (D : D7) : SameField D D :=
  ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun _ _ h => by rw [eq_of_heq h]⟩

end GlobalTheory.TwistChoice

end
