import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtTwistedPlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists

noncomputable section

namespace GlobalTheory.HeightCounting.Up.CopyEx

section Gen

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Rows Formalism.MainNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TwInputs.Move

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

structure Cp (D : D7) {R : Ranks} {H : Host R} {r : Rows.Data R} [NumberField r.LL] [StarRing r.LL] {L : IntermediateField ℚ r.LL}
    {N : NData R H r} (e : ↥L ≃+* ↥D.LL0) (X : NTw R H r L N) (Y : NExp R H r L N X) : Prop where
  xcc : HEq D.ntw.cc X.cc
  xTw : HEq D.ntw.Tw X.Tw
  xl : HEq D.ntw.l X.l
  fixedFieldTransport_baseIntegerRing_heq : HEq D.ntw.O0 X.O0
  fixedFieldTransport_baseIntegerCommRing_heq : HEq D.ntw.crO0 X.crO0
  fixedFieldTransport_baseIntegerAlgebra_heq : HEq D.ntw.algO0 X.algO0
  fixedFieldTransport_baseIntegerTopology_heq : HEq D.ntw.topO0 X.topO0
  xO : HEq D.ntw.O X.O
  xcrO : HEq D.ntw.crO X.crO
  xalgO : HEq D.ntw.algO X.algO
  xOk : HEq D.ntw.Ok X.Ok
  xcrOk : HEq D.ntw.crOk X.crOk
  xalgOk : HEq D.ntw.algOk X.algOk
  xzk : HEq D.ntw.zk X.zk
  xpD : HEq D.ntw.pD X.pD
  xchi1 : HEq D.ntw.chi1 X.chi1
  xSig : HEq D.ntw.Sig X.Sig
  xfinSig : HEq D.ntw.finSig X.finSig
  xjS : HEq D.ntw.jS X.jS
  xside : HEq D.ntw.side X.side
  xrhoS : HEq D.ntw.rhoS X.rhoS
  fixedFieldTransport_initialPlaceSet_heq : HEq D.ntw.S0 X.S0
  xhEig : HEq D.ntw.hEig X.hEig
  xLam : HEq D.ntw.abelian₂ X.abelian₂
  xsideL : HEq D.ntw.sideL X.sideL
  xRCG : HEq D.ntw.RCG X.RCG
  xgrpRCG : HEq D.ntw.grpRCG X.grpRCG
  xfinRCG : HEq D.ntw.finRCG X.finRCG
  xart : HEq D.ntw.art X.art
  xth : HEq D.ntw.th X.th
  xdelta : HEq D.ntw.delta X.delta
  xB : HEq D.ntw.B X.B
  xacgB : HEq D.ntw.acgB X.acgB
  xmodB : HEq D.ntw.modB X.modB
  xTheta : HEq D.ntw.Theta X.Theta
  xhk : HEq D.ntw.hk X.hk
  xThetaPsi : HEq D.ntw.ThetaPsi X.ThetaPsi
  xtopO : HEq D.ntw.topO X.topO
  xfinLam : HEq D.ntw.finLam X.finLam
  xjL : HEq D.ntw.jL X.jL
  xs2 : HEq D.ntw.s2 X.s2
  xlamG : HEq D.ntw.lamG X.lamG
  xXv : HEq D.ntw.Xv X.Xv
  xqs : HEq D.ntw.qs X.qs
  xres : HEq D.ntw.res X.res
  yFm : HEq D.nexp.Fm Y.Fm
  yacgFm : HEq D.nexp.acgFm Y.acgFm
  ymodFmK : HEq D.nexp.modFmK Y.modFmK
  ymodFmO : HEq D.nexp.modFmO Y.modFmO
  yactG : HEq D.nexp.actG Y.actG
  yU : HEq D.nexp.U Y.U
  ypsiU : HEq D.nexp.psiU Y.psiU
  yeAlg : HEq D.nexp.eAlg Y.eAlg
  yDat : HEq D.nexp.Dat Y.Dat
  yth : HEq D.nexp.th Y.th
  ylev : HEq D.nexp.lev Y.lev
  ythPsi : HEq D.nexp.thPsi Y.thPsi
  yMtV : HEq D.nexp.MtV Y.MtV
  yacgMt : HEq D.nexp.acgMt Y.acgMt
  ymodMtK : HEq D.nexp.modMtK Y.modMtK
  ymodMtO : HEq D.nexp.modMtO Y.modMtO
  yMtLat : HEq D.nexp.MtLat Y.MtLat
  ythP : HEq D.nexp.thP Y.thP
  yhkF : HEq D.nexp.hkF Y.hkF
  yBsup : HEq D.nexp.Bsup Y.Bsup
  yembB : HEq D.nexp.embB Y.embB
  ythU : HEq D.nexp.thU Y.thU
  ydelU : HEq D.nexp.delU Y.delU
  ytwPsi : HEq D.nexp.twPsi Y.twPsi
  ytwDel : HEq D.nexp.twDel Y.twDel
  yeH : HEq D.nexp.eH Y.eH
  emb0 : ∀ i i', HEq i i' → ∀ x, HEq (D.ntw.emb0 i (e x)) (X.emb0 i' x)
  emb0b : ∀ i i', HEq i i' → ∀ x, HEq (D.ntw.emb0b i (e x)) (X.emb0b i' x)
  eLL0 : ∀ g g', HEq g g' → e (Y.eLL0 g') = D.nexp.eLL0 g
  grp : G0g D.nd = G0g N
  int : ∀ i i', HEq i i' → ∀ x : L,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i), algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (e x)) ↔
      ∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i'), algebraMap (X.O0 i') (FractionRing (X.O0 i')) y = X.emb0 i' x

theorem exists_cp (D : D7) {R : Ranks} {H : Host R} {r : Rows.Data R} [NumberField r.LL] [StarRing r.LL]
    {L : IntermediateField ℚ r.LL} (N : NData R H r) (hR : D.R = R) (hH : HEq D.host H) (h1 : HEq D.nd.Om N.Om)
    (h2 : HEq D.nd.instOm N.instOm) (h3 : HEq D.nd.algOm N.algOm) (h4 : HEq D.nd.plOm N.plOm) (h5 : HEq D.nd.PlG N.PlG)
    (hE : IsEmpty N.Loc) (e : ↥L ≃+* ↥D.LL0)
    (hs : ∀ x y : L, (y : r.LL) = star (x : r.LL) → (e y : D.what₂.LL) = star (e x : D.what₂.LL)) :
    ∃ (X : NTw R H r L N) (Y : NExp R H r L N X) (_ : NTh R H r L N X Y)
      (br : ∀ (i : X.Tw) (w : PlE H), w ∈ placesOver H.E (X.l i) →
        LocBridge (X.l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) (X.O0 i)),
      (∀ (i : X.Tw) (w : PlE H) (hw : w ∈ placesOver H.E (X.l i)) (x : N.Om), x ∈ N.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1) ∧
        HEq D.ntwbr br ∧ Cp D e X Y := by
  subst hR
  subst hH
  have hP : HEq D.nd.finPlG N.finPlG :=
    Subsingleton.helim (congrArg (fun P : Fin 2 → Type => ∀ k, Fintype (P k)) (eq_of_heq h5)) _ _
  obtain @⟨nOm, ninstOm, nalgOm, nacOm, nplOm, nldat, nsha_eq, nLoc, nl, nlPrime, nj, nj_range, nmu, nw, nw_l, nmu_w,
    nw_tw, nlocs, nlocs_mem, nO, ninstO, ndomO, ndvrO, nalgO, nfinO, ntopO, ntrO, nO_adic, nO_complete, nembK,
    nembK_w, nX, nfinX, nneX, nT, nT_local, nT_sep, nMt, nacgMt, nmodMt, nfreeMt, nfinMt, nact, nact_inj, nprMt,
    nprMt_span, nprMt_lat, neig_ne, nchi, nchi_cont, nchi_def, nZ, nZgood, ns0, ns0_odd, ns0_two, nS, nQ,
    nSQ_split, nSQ_disj, nSQ_l, nS_def, nhT, nT_gen, ngam0, ngam0_mem, ngam0_gen, nchi_ram_Q, nBj, nacgBj, nmodBj,
    nfreeBj, nfinBj, ng_split, nPlG, nfinPlG, ncard_PlG, nlab, nlab_monic, nchiT, ncardG0g_eq⟩ := N
  obtain rfl : D.nd.Om = nOm := eq_of_heq h1
  obtain rfl : D.nd.instOm = ninstOm := eq_of_heq h2
  obtain rfl : D.nd.algOm = nalgOm := eq_of_heq h3
  obtain rfl : D.nd.plOm = nplOm := eq_of_heq h4
  obtain rfl : D.nd.PlG = nPlG := eq_of_heq h5
  obtain rfl : D.nd.finPlG = nfinPlG := eq_of_heq hP
  let N : NData D.R D.host r := @NData.mk _ _ _ D.nd.Om D.nd.instOm D.nd.algOm nacOm D.nd.plOm nldat nsha_eq nLoc nl nlPrime nj nj_range nmu nw nw_l nmu_w
    nw_tw nlocs nlocs_mem nO ninstO ndomO ndvrO nalgO nfinO ntopO ntrO nO_adic nO_complete nembK nembK_w nX nfinX
    nneX nT nT_local nT_sep nMt nacgMt nmodMt nfreeMt nfinMt nact nact_inj nprMt nprMt_span nprMt_lat neig_ne nchi
    nchi_cont nchi_def nZ nZgood ns0 ns0_odd ns0_two nS nQ nSQ_split nSQ_disj nSQ_l nS_def nhT nT_gen ngam0
    ngam0_mem ngam0_gen nchi_ram_Q nBj nacgBj nmodBj nfreeBj nfinBj ng_split D.nd.PlG D.nd.finPlG ncard_PlG nlab
    nlab_monic nchiT ncardG0g_eq
  have hE : IsEmpty N.Loc := hE
  let X : NTw D.R D.host r L N :=
    { D.ntw with
      emb0 := fun i => (D.ntw.emb0 i).comp e.toRingHom
      emb0b := fun i => (D.ntw.emb0b i).comp e.toRingHom
      restX_coefficientEmbedding_conj := fun i x y h => D.ntw.restX_coefficientEmbedding_conj i _ _ (hs x y h)
      twOf := fun a => hE.elim a
      twSide := fun a => hE.elim a
      twOf_l := fun a => hE.elim a
      twist₂ := fun a => hE.elim a
      twO_emb := fun a => hE.elim a
      psiL := fun a => hE.elim a
      psiL_ord := fun a => hE.elim a
      psiL_open := fun a => hE.elim a
      psiL_anti := fun a => hE.elim a
      psiL_ram := fun a => hE.elim a
      psiL_l := fun a => hE.elim a
      chi_tw := fun a => hE.elim a }
  let Y : NExp D.R D.host r L N X :=
    { D.nexp with
      eLL0 := fun g => e.symm (D.nexp.eLL0 g)
      eAlg_def := fun i b g => by
        refine (D.nexp.eAlg_def i b g).trans ?_
        cases b
        · exact congrArg (fun z => IsFractionRing.map (D.ntw.O_inj i) (D.ntw.emb0b i z)) (e.apply_symm_apply _).symm
        · exact congrArg (fun z => IsFractionRing.map (D.ntw.O_inj i) (D.ntw.emb0 i z)) (e.apply_symm_apply _).symm }
  let T : NTh D.R D.host r L N X Y := { D.nth with }
  refine ⟨X, Y, T, D.ntwbr, D.ntwbr_ind, HEq.rfl, ?_⟩
  exact {
    xcc := HEq.rfl
    xTw := HEq.rfl
    xl := HEq.rfl
    fixedFieldTransport_baseIntegerRing_heq := HEq.rfl
    fixedFieldTransport_baseIntegerCommRing_heq := HEq.rfl
    fixedFieldTransport_baseIntegerAlgebra_heq := HEq.rfl
    fixedFieldTransport_baseIntegerTopology_heq := HEq.rfl
    xO := HEq.rfl
    xcrO := HEq.rfl
    xalgO := HEq.rfl
    xOk := HEq.rfl
    xcrOk := HEq.rfl
    xalgOk := HEq.rfl
    xzk := HEq.rfl
    xpD := HEq.rfl
    xchi1 := HEq.rfl
    xSig := HEq.rfl
    xfinSig := HEq.rfl
    xjS := HEq.rfl
    xside := HEq.rfl
    xrhoS := HEq.rfl
    fixedFieldTransport_initialPlaceSet_heq := HEq.rfl
    xhEig := HEq.rfl
    xLam := HEq.rfl
    xsideL := HEq.rfl
    xRCG := HEq.rfl
    xgrpRCG := HEq.rfl
    xfinRCG := HEq.rfl
    xart := HEq.rfl
    xth := HEq.rfl
    xdelta := HEq.rfl
    xB := HEq.rfl
    xacgB := HEq.rfl
    xmodB := HEq.rfl
    xTheta := HEq.rfl
    xhk := HEq.rfl
    xThetaPsi := HEq.rfl
    xtopO := HEq.rfl
    xfinLam := HEq.rfl
    xjL := HEq.rfl
    xs2 := HEq.rfl
    xlamG := HEq.rfl
    xXv := HEq.rfl
    xqs := HEq.rfl
    xres := HEq.rfl
    yFm := HEq.rfl
    yacgFm := HEq.rfl
    ymodFmK := HEq.rfl
    ymodFmO := HEq.rfl
    yactG := HEq.rfl
    yU := HEq.rfl
    ypsiU := HEq.rfl
    yeAlg := HEq.rfl
    yDat := HEq.rfl
    yth := HEq.rfl
    ylev := HEq.rfl
    ythPsi := HEq.rfl
    yMtV := HEq.rfl
    yacgMt := HEq.rfl
    ymodMtK := HEq.rfl
    ymodMtO := HEq.rfl
    yMtLat := HEq.rfl
    ythP := HEq.rfl
    yhkF := HEq.rfl
    yBsup := HEq.rfl
    yembB := HEq.rfl
    ythU := HEq.rfl
    ydelU := HEq.rfl
    ytwPsi := HEq.rfl
    ytwDel := HEq.rfl
    yeH := HEq.rfl
    emb0 := fun _ _ h _ => by cases h; rfl
    emb0b := fun _ _ h _ => by cases h; rfl
    eLL0 := fun _ _ h => by cases h; exact e.apply_symm_apply _
    grp := rfl
    int := fun _ _ h _ => by cases h; rfl }

theorem exists_copyN (D D' : D7) (hg : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd) (hE : IsEmpty D'.nd.Loc)
    (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) (hι : ∀ x, D'.what₂.embLL (ι x) = D.what₂.embLL x)
    (he : ∀ x : ↥D'.LL0, ι (e x : D.what₂.LL) = (x : D'.what₂.LL))
    (h0 : ∀ g g', HEq g g' → D.ntypes.e0.coeff g = D'.ntypes.e0.coeff g') (av : avPrimes D = avPrimes D')
    (sp : HEq D.sp D'.sp) (Tau : D.what₂.Tau = D'.what₂.Tau) (eTau : HEq D.eTau D'.eTau) (hc : HEq D.hc D'.hc)
    (u : D'.what₂.places.Pl → D.what₂.places.Pl) (hu : Function.Surjective u) (ht : ∀ v, TwistedAt D (u v) ↔ TwistedAt D' v)
    (hv : ∀ v (x : 𝓞 ↥D.LL0) (x' : 𝓞 ↥D'.LL0), e (x' : ↥D'.LL0) = (x : ↥D.LL0) →
      (0 < D.what₂.places.val (u v) ((x : ↥D.LL0) : D.what₂.LL) ↔ 0 < D'.what₂.places.val v ((x' : ↥D'.LL0) : D'.what₂.LL))) :
    ∃ N : TwNew D', CopyN D N ι e := by
  have hs : ∀ x y : ↥D'.LL0, (y : D'.what₂.LL) = star (x : D'.what₂.LL) → (e y : D.what₂.LL) = star (e x : D.what₂.LL) := fun x y h =>
    D.what₂.embLL.injective (by rw [D.starLL_cx, ← hι, ← hι, he, he, h, D'.starLL_cx])
  obtain ⟨X, Y, T, br, hbr, hb, c⟩ := exists_cp D D'.nd hg.R hg.host hg.Om hg.instOm hg.algOm hg.plOm hg.PlG hE e hs
  have hh : ∀ g : G0g D'.nd, D'.what₂.embLL ((Y.eLL0 g : ↥D'.LL0) : D'.what₂.LL) = D'.ntypes.e0.coeff g := fun g => by
    have hg' : HEq (cast c.grp.symm g) g := cast_heq _ _
    rw [← he, hι, c.eLL0 _ _ hg', D.nStage_trivialCharacter_coeff_eq, h0 _ _ hg']
  refine ⟨⟨X, Y, hh, T, br, hbr⟩, ⟨⟨⟨hg.R, hg.host, hg.loc, hg.Om, hg.instOm, hg.algOm, hg.plOm, hg.PlG⟩,
    ⟨c.xcc, c.xTw, c.xl, c.fixedFieldTransport_baseIntegerRing_heq, c.fixedFieldTransport_baseIntegerCommRing_heq, c.fixedFieldTransport_baseIntegerAlgebra_heq, c.fixedFieldTransport_baseIntegerTopology_heq, c.xO, c.xcrO, c.xalgO, c.xOk, c.xcrOk, c.xalgOk, c.xzk, c.xpD, c.xchi1, c.xSig, c.xfinSig, c.xjS, c.xside, c.xrhoS, c.fixedFieldTransport_initialPlaceSet_heq, c.xhEig, c.xLam, c.xsideL, c.xRCG, c.xgrpRCG, c.xfinRCG, c.xart, c.xth⟩,
    ⟨c.yFm, c.yacgFm, c.ymodFmK, c.ymodFmO, c.yactG, c.yU, c.ypsiU, c.yeAlg, c.yDat, c.yth, c.ylev, c.ythPsi, c.yMtV, c.yacgMt, c.ymodMtK, c.ymodMtO, c.yMtLat, c.ythP, c.yhkF⟩, hb, av⟩,
    sp, Tau, eTau, hc, hι, he, c.emb0, c.emb0b, fun i i' hi => ?_, c.xdelta, c.xB, c.xacgB, c.xmodB, c.xTheta, c.xhk,
    c.yBsup, c.yembB, c.ythU, c.ydelU⟩, c.xThetaPsi, c.xtopO, c.xfinLam, c.xjL, c.xs2, c.xlamG, c.xXv, c.xqs, c.xres, c.eLL0,
    c.ytwPsi, c.ytwDel, c.yeH⟩
  change D.ntw.NonzeroIndexPlace i ↔ X.NonzeroIndexPlace i'
  constructor
  · rintro ⟨v, h1, h2⟩
    obtain ⟨v, rfl⟩ := hu v
    exact ⟨v, (ht v).1 h1, fun x' => (c.int i i' hi x').symm.trans
      ((h2 (RingOfIntegers.mapRingHom e.toRingHom x')).trans (hv v _ x' rfl))⟩
  · rintro ⟨v, h1, h2⟩
    refine ⟨u v, (ht v).2 h1, fun x => ?_⟩
    have hx : e ((RingOfIntegers.mapRingHom e.symm.toRingHom x : 𝓞 ↥D'.LL0) : ↥D'.LL0) = (x : ↥D.LL0) := e.apply_symm_apply _
    have h3 := (c.int i i' hi _).trans ((h2 (RingOfIntegers.mapRingHom e.symm.toRingHom x)).trans (hv v x _ hx).symm)
    rwa [hx] at h3

end Gen

section Types

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem.Top

theorem trueTypesIdempotent_coeff_heq {R R' : Ranks} {H : Host R} {H' : Host R'} {r : Rows.Data R} {r' : Rows.Data R'} {N : NData R H r}
    {N' : NData R' H' r'} {A : NAut N} {A' : NAut N'} {T : NTypes A} {T' : NTypes A'} {P : Formalism.L2.Host.PiBar H}
    {P' : Formalism.L2.Host.PiBar H'} {W : Formalism.L2.Host.Omg H} {W' : Formalism.L2.Host.Omg H'} (hR : R = R') (hH : HEq H H') (hP : HEq P P')
    (hW : HEq W W') (h : TypesTrue T P W) (h' : TypesTrue T' P' W') (hG : N.PlG = N'.PlG) (hp : HEq A.plGw A'.plGw)
    (g : G0g N) (g' : G0g N') (hg : HEq g g') : T.e0.coeff g = T'.e0.coeff g' := by
  subst hR
  subst hH
  subst hP
  subst hW
  rw [← h.typeIdempotent_coeff_across_layers h' g]
  congr 1
  have key : ∀ {Q Q' : Fin 2 → Type} (_ : Q = Q') {Z : Type} {Y : Fin 2 → Type} (a : ∀ k, Q k → Z) (a' : ∀ k, Q' k → Z)
      (_ : HEq a a') (_ : ∀ k, Function.Injective (a k)) (u : ∀ kv : (Σ k, Q k), Y kv.1) (u' : ∀ kv : (Σ k, Q' k), Y kv.1)
      (_ : HEq u u') (k : Fin 2) (v : Q k) (v' : Q' k), a' k v' = a k v → u ⟨k, v⟩ = u' ⟨k, v'⟩ := by
    intro Q Q' e Z Y a a' ha hi u u' hu k v v' hv
    subst e
    cases ha
    cases hu
    rw [hi k hv]
  funext ⟨k, v'⟩
  rw [grpEquiv_apply]
  refine key hG (Y := fun k => GL (Fin R.r) (ZMod (H.g k))) A.plGw A'.plGw hp A.plGw_inj g g' hg k _ v' ?_
  rw [← h.plGw_plEquiv h', Equiv.apply_symm_apply]

end Types

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder plUnder_surjective)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem exists_fixedEquiv {B B' : Base} (h : Enl B B') :
    ∃ e : ↥B'.LL0 ≃+* ↥B.LL0, ∀ x : ↥B'.LL0, incl h (e x : B.LL) = (x : B'.LL) := by
  have hm : ∀ x : B.LL0, incl h (x : B.LL) ∈ B'.LL0 := fun x => by
    obtain ⟨y, hy, e⟩ : B.embLL (x : B.LL) ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := h.2.2.1 ▸ ⟨x, x.2, rfl⟩
    rwa [← B'.embLL.injective (e.trans (embLL_incl h _).symm)]
  let j : B.LL0 →+* B'.LL0 := ((incl h).comp B.LL0.val.toRingHom).codRestrict B'.LL0 hm
  have hj : Function.Surjective j := fun x' => by
    obtain ⟨y, hy, e⟩ : B'.embLL (x' : B'.LL) ∈ B.embLL '' (B.LL0 : Set B.LL) := h.2.2.1 ▸ ⟨x', x'.2, rfl⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (B'.embLL.injective ((embLL_incl h y).trans e))⟩
  exact ⟨(RingEquiv.ofBijective j ⟨j.injective, hj⟩).symm,
    fun x => congrArg Subtype.val ((RingEquiv.ofBijective j ⟨j.injective, hj⟩).apply_symm_apply x)⟩

theorem same_pre (X X' : Stages) (h : X'.B.toPre = X.B.toPre) : avPrimes X.toD7 = avPrimes X'.toD7 ∧ HEq X.toD7.sp X'.toD7.sp ∧
    X.toD7.what₂.Tau = X'.toD7.what₂.Tau ∧ HEq X.toD7.eTau X'.toD7.eTau ∧ HEq X.toD7.hc X'.toD7.hc := by
  have e1 : (fun u => (X.toD7.mem u).A.T) = X.B.T := funext X.C.A_T
  have e2 : (fun u => (X'.toD7.mem u).A.T) = X'.B.T := funext X'.C.A_T
  unfold avPrimes
  rw [e1, e2]
  clear e1 e2
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  cases B'
  dsimp only at h
  subst h
  exact ⟨rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem frame_heq {P P' : Pre} (h : P' = P) {f : Top.Fr P} {f' : Top.Fr P'} (hf : HEq f' f) : HEq f.P f'.P ∧ HEq f.W f'.W := by
  subst h
  cases hf
  exact ⟨HEq.rfl, HEq.rfl⟩

variable {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'}

theorem mem_Wt_iff (h : Enl B B') {P : Pre2 K w} {P' : Pre2 K w'} (hx : Ext P.z P'.z) (v' : B'.places.Pl) :
    plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt := by
  have hB : Below (w.D P.Z₀) (w'.D P'.Z₀) (plUnder h v') v' := fun x x' e => by
    have : x' = RingOfIntegers.mapRingHom (incl h) x :=
      RingOfIntegers.ext (B'.embLL.injective (e.symm.trans (embLL_incl h _).symm))
    subst this
    exact mem_plUnder h v' x
  have h0 := hx.W1 _ v' hB
  have a := Dat.mem_auxiliaryPlaces_iff_three_parts P.z (fun _ _ => 0) (plUnder h v')
  have b := Dat.mem_auxiliaryPlaces_iff_three_parts P'.z (fun _ _ => 0) v'
  have i0 : (plUnder h v' ∈ P.z.IwasawaPlaceIndex ∨ plUnder h v' ∈ P.z.W1jw) ↔ (v' ∈ P'.z.IwasawaPlaceIndex ∨ v' ∈ P'.z.W1jw) :=
    ⟨fun h => (b.1 (h0.1 (a.2 (Or.inl h)))).resolve_right (Second.not_mem_W1F_zero _ _),
      fun h => (a.1 (h0.2 (b.2 (Or.inl h)))).resolve_right (Second.not_mem_W1F_zero _ _)⟩
  have c := Dat.mem_auxiliaryPlaces_iff_three_parts P.z (F0K K.s (w.D P.Z₀)) (plUnder h v')
  have d := Dat.mem_auxiliaryPlaces_iff_three_parts P'.z (F0K K.s (w'.D P'.Z₀)) v'
  have e := nonzeroForcedContentPlaces_agree_over_enlargement K B f T w B' f' T' w' h P.Z₀ P'.Z₀ P.kap P'.kap _ v' hB
  exact (iff_of_eq (congrArg (plUnder h v' ∈ ·) P.exact)).trans
    ((c.trans ((or_congr i0 e).trans d.symm)).trans (iff_of_eq (congrArg (v' ∈ ·) P'.exact)).symm)

theorem val_pos_plUnder (X X' : Stages) (h : Enl X.B X'.B) (v' : X'.B.places.Pl) (x : 𝓞 ↥X.toD7.LL0) (x' : 𝓞 ↥X'.toD7.LL0)
    (e : incl h ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) = ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL)) :
    0 < X.toD7.what₂.places.val (plUnder h v') ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) ↔
      0 < X'.toD7.what₂.places.val v' ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := by
  have hmap : RingOfIntegers.mapRingHom (incl h) (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x) =
      algebraMap (𝓞 ↥X'.toD7.LL0) (𝓞 X'.toD7.what₂.LL) x' := RingOfIntegers.ext e
  refine (TwistChoice.val_pos_iff_mem X.toD7 (plUnder h v') x).trans
    (Iff.trans ?_ (TwistChoice.val_pos_iff_mem X'.toD7 v' x').symm)
  have hm := mem_plUnder h v' (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x)
  rw [hmap] at hm
  exact hm

theorem exists_copy_st (h : Enl B B') (hf : HEq f' f) {P : Pre2 K w} (x : St P) {P' : Pre2 K w'} (hx : Ext P.z P'.z) (x' : St P')
    (hE : IsEmpty (Dof x').nd.Loc) (hg : SameGal (Dof x) (Dof x')) :
    ∃ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e := by
  obtain ⟨e, he⟩ := exists_fixedEquiv h
  obtain ⟨a1, a2, a3, a4, a5⟩ := same_pre (w.st x.o.Z) (w'.st x'.o.Z) h.1
  obtain ⟨N, hN⟩ := exists_copyN (Dof x) (Dof x') hg.gal hE (incl h) e (embLL_incl h) he
    (trueTypesIdempotent_coeff_heq hg.gal.R hg.gal.host (frame_heq h.1 hf).1 (frame_heq h.1 hf).2 x.fits.grp x'.fits.grp (eq_of_heq hg.gal.PlG) hg.pl)
    a1 a2 a3 a4 a5 (plUnder h) (plUnder_surjective h)
    (fun v => (Model.twisted_iff x _).trans ((mem_Wt_iff h hx v).trans (Model.twisted_iff x' v).symm))
    fun v y y' hy => val_pos_plUnder (w.st x.o.Z) (w'.st x'.o.Z) h v y y'
      ((congrArg (fun z : ↥B.LL0 => incl h (z : B.LL)) hy).symm.trans (he _))
  exact ⟨N, incl h, e, hN⟩

theorem exists_copy : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∃ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hf _ _ _ _ _ _ x _ _ hx x' l' hg => exists_copy_st h hf x hx x' l'.a.A.bare hg

end GlobalTheory.HeightCounting.Up.CopyEx

end
