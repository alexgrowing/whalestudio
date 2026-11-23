import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ActEqZeroOfQK
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg

section Layer

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

open Classical in
set_option maxHeartbeats 2000000 in

def ndCut (N : NData R H what₂) (keep : N.Loc → Prop) (Xs : ∀ i, Set (N.X i)) (ne : ∀ i, keep i → (Xs i).Nonempty) :
    NData R H what₂ :=
  { N with
    Loc := {i // keep i}
    locs := fun j w => (N.locs j w).subtype keep
    locs_mem := fun j w i => Finset.mem_subtype.trans (N.locs_mem j w i.1)
    l := fun i => @NData.l R H what₂ N i.1
    lPrime := fun i => @NData.lPrime R H what₂ N i.1
    j := fun i => @NData.j R H what₂ N i.1
    j_range := fun i => @NData.j_range R H what₂ N i.1
    mu := fun i => @NData.mu R H what₂ N i.1
    w := fun i => @NData.w R H what₂ N i.1
    w_l := fun i => @NData.w_l R H what₂ N i.1
    mu_w := fun i => @NData.mu_w R H what₂ N i.1
    w_tw := fun i => @NData.w_tw R H what₂ N i.1
    O := fun i => @NData.O R H what₂ N i.1
    instO := fun i => @NData.instO R H what₂ N i.1
    domO := fun i => @NData.domO R H what₂ N i.1
    dvrO := fun i => @NData.dvrO R H what₂ N i.1
    algO := fun i => @NData.algO R H what₂ N i.1
    finO := fun i => @NData.finO R H what₂ N i.1
    topO := fun i => @NData.topO R H what₂ N i.1
    trO := fun i => @NData.trO R H what₂ N i.1
    O_adic := fun i => @NData.O_adic R H what₂ N i.1
    O_complete := fun i => @NData.O_complete R H what₂ N i.1
    embK := fun i => @NData.embK R H what₂ N i.1
    embK_w := fun i => @NData.embK_w R H what₂ N i.1
    chi := fun i => @NData.chi R H what₂ N i.1
    chi_cont := fun i => @NData.chi_cont R H what₂ N i.1
    chi_def := fun i => @NData.chi_def R H what₂ N i.1
    s0 := fun i => @NData.s0 R H what₂ N i.1
    restNLevelExponent_of_odd := fun i => @NData.restNLevelExponent_of_odd R H what₂ N i.1
    restNLevelExponent_of_two := fun i => @NData.restNLevelExponent_of_two R H what₂ N i.1
    S := fun i => @NData.S R H what₂ N i.1
    Q := fun i => @NData.Q R H what₂ N i.1
    SQ_split := fun i => @NData.SQ_split R H what₂ N i.1
    SQ_disj := fun i => @NData.SQ_disj R H what₂ N i.1
    SQ_l := fun i => @NData.SQ_l R H what₂ N i.1
    S_def := fun i => @NData.S_def R H what₂ N i.1
    gam0 := fun i => @NData.gam0 R H what₂ N i.1
    locNd_chebotarevPlace_mem := fun i => @NData.locNd_chebotarevPlace_mem R H what₂ N i.1
    restN_tameGenerator_generates := fun i => @NData.restN_tameGenerator_generates R H what₂ N i.1
    chi_ram_Q := fun i => @NData.chi_ram_Q R H what₂ N i.1
    Bj := fun i => @NData.Bj R H what₂ N i.1
    acgBj := fun i => @NData.acgBj R H what₂ N i.1
    modBj := fun i => @NData.modBj R H what₂ N i.1
    freeBj := fun i => @NData.freeBj R H what₂ N i.1
    finBj := fun i => @NData.finBj R H what₂ N i.1
    X := fun i => Xs i.1
    finX := fun i => Fintype.ofFinite _
    neX := fun i => (ne i.1 i.2).to_subtype
    T := fun i => cutT (N.T i.1) (Xs i.1)
    T_local := fun i => by
      haveI := (ne i.1 i.2).to_subtype; haveI := N.T_local i.1
      exact cutT_local _ _
    T_sep := fun i x y h => by
      obtain ⟨f, hf, e⟩ := N.T_sep i.1 x.1 y.1 (fun k => h (Subtype.ext k))
      exact ⟨_, ⟨f, hf, rfl⟩, e⟩
    Mt := fun i => cutM (N.T i.1) (N.act i.1) (Xs i.1)
    acgMt := fun i => inferInstance
    modMt := fun i => inferInstance
    freeMt := fun i => cutM_free _ _ _
    finMt := fun i => inferInstance
    act := fun i => cutAct (N.T i.1) (N.act i.1) (Xs i.1)
    act_inj := fun i => cutAct_inj _ _ _ (N.T_sep i.1) (N.act_inj i.1)
    prMt := fun i => (qK (N.T i.1) (N.act i.1) (Xs i.1)).comp (N.prMt i.1)
    prMt_span := fun i => by
      have := congrArg (Submodule.map (qK (N.T i.1) (N.act i.1) (Xs i.1))) (N.prMt_span i.1)
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearMap.range_eq_top.2 (qK_surj _ _ _)] at this
      exact this
    prMt_lat := fun i => by
      have := congrArg (Submodule.map ((qK (N.T i.1) (N.act i.1) (Xs i.1)).restrictScalars (N.O i.1))) (N.prMt_lat i.1)
      rw [Submodule.map_span, ← Set.image_comp] at this
      refine Eq.trans this ?_
      ext v
      constructor
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
        exact ⟨_, (qK_tmul _ _ _ 1 m).symm⟩
      · rintro ⟨m, rfl⟩
        obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
        exact ⟨_, ⟨m, rfl⟩, qK_tmul _ _ _ 1 m⟩
    eig_ne := fun i x => Alg.eig_ne _ _ _ (N.T_sep i.1) x (N.eig_ne i.1 x.1)
    Z := fun i => (N.Z i.1).subtype _
    Zgood := fun i => (N.Zgood i.1).subtype _
    hT := fun i v k => resT _ _ (N.hT i.1 v k)
    T_gen := fun i => by
      have := congrArg (Subalgebra.map (resA (N.O i.1) (Xs i.1))) (N.T_gen i.1)
      rw [AlgHom.map_adjoin] at this
      refine Eq.trans (congrArg _ ?_) this
      ext f
      constructor
      · rintro ⟨v, k, a, b, c, d, e, g, rfl⟩
        exact ⟨_, ⟨v, k, a, b, c, d, e, g, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, k, a, b, c, d, e, g, rfl⟩, rfl⟩
        exact ⟨v, k, a, b, c, d, e, g, rfl⟩ }

open Classical in

def optIn {X : Type} (S : Set X) (o : Option X) : Option S := o.bind fun x => if h : x ∈ S then some ⟨x, h⟩ else none

theorem optIn_eq_some {X : Type} {S : Set X} {o : Option X} {x : S} : optIn S o = some x ↔ o = some x.1 := by
  cases o with
  | none => simp [optIn]
  | some y =>
    simp only [optIn, Option.bind_some, Option.some.injEq]
    split_ifs with h
    · simp [Subtype.ext_iff]
    · simp only [false_iff]; rintro rfl; exact h x.2

set_option maxHeartbeats 2000000 in

def nautCut {N : NData R H what₂} (A : NAut N) (keep : N.Loc → Prop) (Xs : ∀ i, Set (N.X i))
    (ne : ∀ i, keep i → (Xs i).Nonempty) : NAut (ndCut N keep Xs ne) :=
  { A with
    iotaQ := fun i => @NAut.iotaQ R H what₂ N A i.1
    iotaQC := fun i => @NAut.iotaQC R H what₂ N A i.1
    iota_LL := fun i => @NAut.iota_LL R H what₂ N A i.1
    iotaQ_alg := fun i => @NAut.iotaQ_alg R H what₂ N A i.1
    muC := fun i => @NAut.muC R H what₂ N A i.1
    muC_csd := fun i => @NAut.muC_csd R H what₂ N A i.1
    AV := fun i => @NAut.AV R H what₂ N A i.1
    finAV := fun i => @NAut.finAV R H what₂ N A i.1
    typeV := fun i => @NAut.typeV R H what₂ N A i.1
    typeV_ne := fun i => @NAut.typeV_ne R H what₂ N A i.1
    typeV_indep := fun i => @NAut.typeV_indep R H what₂ N A i.1
    typeV_top := fun i => @NAut.typeV_top R H what₂ N A i.1
    locV := fun i => @NAut.locV R H what₂ N A i.1
    satV := fun i => @NAut.satV R H what₂ N A i.1
    locV_unr := fun i => @NAut.locV_unr R H what₂ N A i.1
    infWt := fun i => @NAut.infWt R H what₂ N A i.1
    locW := fun i => @NAut.locW R H what₂ N A i.1
    satW := fun i => @NAut.satW R H what₂ N A i.1
    lab_loc := fun i => @NAut.lab_loc R H what₂ N A i.1
    wdOf := fun i => @NAut.wdOf R H what₂ N A i.1
    wdOf_dim := fun i => @NAut.wdOf_dim R H what₂ N A i.1
    wdOf_unr := fun i => @NAut.wdOf_unr R H what₂ N A i.1
    wdOf_frob := fun i => @NAut.wdOf_frob R H what₂ N A i.1
    wdOf_ine := fun i => @NAut.wdOf_ine R H what₂ N A i.1
    wdOf_mono0 := fun i => @NAut.wdOf_mono0 R H what₂ N A i.1
    IsCrysW := fun i => @NAut.IsCrysW R H what₂ N A i.1
    IsPotCrysW := fun i => @NAut.IsPotCrysW R H what₂ N A i.1
    IsdRW := fun i => @NAut.IsdRW R H what₂ N A i.1
    jumpsW := fun i => @NAut.jumpsW R H what₂ N A i.1
    wdOf_unrL := fun i => @NAut.wdOf_unrL R H what₂ N A i.1
    wdOf_mono0L := fun i => @NAut.wdOf_mono0L R H what₂ N A i.1
    jumpsInf := fun i => @NAut.jumpsInf R H what₂ N A i.1
    locAutHodgeTateWeightsLevelZero := fun i => @NAut.locAutHodgeTateWeightsLevelZero R H what₂ N A i.1
    jumpsInf_def := fun i => @NAut.jumpsInf_def R H what₂ N A i.1
    locAut_hodgeTateWeightsLevelZero_def := fun i => @NAut.locAut_hodgeTateWeightsLevelZero_def R H what₂ N A i.1
    chi_mu := fun i => @NAut.chi_mu R H what₂ N A i.1
    kFbar := fun i => @NAut.kFbar R H what₂ N A i.1
    ptV := fun i P => optIn (Xs i.1) (A.ptV i.1 P)
    pt_surj := fun i x => (A.pt_surj i.1 x.1).imp fun _ h => optIn_eq_some.2 h
    eig_dim := fun i x => by
      have e : {P | optIn (Xs i.1) (A.ptV i.1 P) = some x} = {P | A.ptV i.1 P = some x.1} := Set.ext fun _ => optIn_eq_some
      refine (mult_eq _ _ _ (N.T_sep i.1) x).trans ((A.eig_dim i.1 x.1).trans ?_)
      rw [← e]; rfl
    pt_loc := fun i P x h => A.pt_loc i.1 P x.1 (optIn_eq_some.1 h) }

end Layer

set_option maxHeartbeats 4000000 in

def layCut (D : D7) (c : CutD D) : Lay0 D :=
  { loc := D.loc, locA := D.locA, locT := D.locT
    nd := ndCut D.nd c.keep c.Xs c.ne
    ntw := { D.ntw with
      twOf := fun i => D.ntw.twOf i.1
      twSide := fun i => D.ntw.twSide i.1
      psiL := fun i => D.ntw.psiL i.1
      twOf_l := fun i => D.ntw.twOf_l i.1
      twist₂ := fun i => D.ntw.twist₂ i.1
      twO_emb := fun i => D.ntw.twO_emb i.1
      psiL_ord := fun i => D.ntw.psiL_ord i.1
      psiL_open := fun i => D.ntw.psiL_open i.1
      psiL_anti := fun i => D.ntw.psiL_anti i.1
      psiL_ram := fun i => D.ntw.psiL_ram i.1
      psiL_l := fun i => D.ntw.psiL_l i.1
      chi_tw := fun i => D.ntw.chi_tw i.1 }
    naut := nautCut D.naut c.keep c.Xs c.ne
    nbc := { D.nbc with
      embAV := fun i => D.nbc.embAV i.1
      embAV_inj := fun i => D.nbc.embAV_inj i.1
      embAV_loc := fun i => D.nbc.embAV_loc i.1
      embAV_sat := fun i => D.nbc.embAV_sat i.1
      embAV_sph := fun i => D.nbc.embAV_sph i.1
      embAV_inf := fun i => D.nbc.embAV_inf i.1 }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with
      heckeLoc_gamma_places := fun i => D.ntypes.heckeLoc_gamma_places i.1
      chiT_tg := fun i => D.ntypes.chiT_tg i.1 }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    nth := { D.nth with }
    nbr := fun i => D.nbr i.1, nbr_ind := fun i => D.nbr_ind i.1, self_good := fun i => D.self_good i.1
    ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind
    loc_tie := fun i => D.loc_tie i.1, bc_tie := fun i => D.bc_tie i.1, rbar_tie := fun i => D.rbar_tie i.1
    mtpar_tie := fun i => D.mtpar_tie i.1 }

theorem layerCut_admissible (D : D7) (c : CutD D) : (layCut D c).ZOk := by
  classical
  have z : ∀ (i : {i // c.keep i}) (x : c.Xs i.1), x ∈ ZN (layCut D c).nd (layCut D c).naut i ↔ x.1 ∈ ZN D.nd D.naut i.1 :=
    fun i x => exists_congr fun P => and_congr optIn_eq_some Iff.rfl
  refine ⟨fun i x => ?_, fun i x => ?_⟩
  · exact (Finset.mem_subtype.trans (D.Z_tie i.1 x.1)).trans (z i x).symm
  · refine (Finset.mem_subtype.trans (D.Zgood_tie i.1 x.1)).trans (and_congr (z i x).symm ?_)
    exact exists_congr fun Sig => and_congr (exists_congr fun P => and_congr optIn_eq_some.symm Iff.rfl) Iff.rfl

def cut (D : D7) (c : CutD D) : D7 :=
  setRaw D (layCut D c).eta (layCut D c).eta_nonneg ((layCut D c).reEta _ (layCut D c).eta_nonneg)
    ((layerCut_admissible D c).reEta _ _) (layCut D c).etaOk_reEta

end UpperTheory.GalC
