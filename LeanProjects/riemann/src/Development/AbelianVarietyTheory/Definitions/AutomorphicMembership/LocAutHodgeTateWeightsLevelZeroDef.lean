import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL}

set_option synthInstance.maxHeartbeats 400000 in

structure LocNd (L : NLay0 R H what₂ LL0) where
  Loc : Type
  l : Loc → ℕ
  [lPrime : ∀ i, Fact (l i).Prime]
  j : Loc → ℕ
  j_range : ∀ i, 1 ≤ j i ∧ j i ≤ R.m
  mu : Loc → what₂.Tup
  w : Loc → what₂.places.Pl
  w_l : ∀ i, what₂.places.resChar (w i) = l i
  mu_w : ∀ i, mu i = what₂.muTw (w i)
  w_tw : ∀ i, what₂.muAt (w i) ≠ what₂.mu0
  locs : ℕ → what₂.places.Pl → Finset Loc
  locs_mem : ∀ j' w' i, i ∈ locs j' w' ↔ j i = j' ∧ w i = w'
  O : Loc → Type
  [instO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]
  [dvrO : ∀ i, IsDiscreteValuationRing (O i)]
  [algO : ∀ i, Algebra ℤ_[l i] (O i)]
  [finO : ∀ i, Module.Finite ℤ_[l i] (O i)]
  [topO : ∀ i, TopologicalSpace (O i)]
  [trO : ∀ i, IsTopologicalRing (O i)]
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)
  embK : ∀ i, what₂.LL →+* FractionRing (O i)
  embK_w : ∀ i (x : what₂.LL), 0 ≤ what₂.places.val (w i) x ↔
    embK i x ∈ (algebraMap (O i) (FractionRing (O i))).range
  X : Loc → Type
  [finX : ∀ i, Fintype (X i)]
  [neX : ∀ i, Nonempty (X i)]
  T : ∀ i, Subalgebra (O i) (X i → O i)
  T_local : ∀ i, IsLocalRing (T i)
  T_sep : ∀ i (x y : X i), x ≠ y → ∃ f ∈ T i, (f : X i → O i) x ≠ (f : X i → O i) y
  Mt : Loc → Type
  [acgMt : ∀ i, AddCommGroup (Mt i)]
  [modMt : ∀ i, Module (O i) (Mt i)]
  [freeMt : ∀ i, Module.Free (O i) (Mt i)]
  [finMt : ∀ i, Module.Finite (O i) (Mt i)]
  act : ∀ i, T i →ₐ[O i] Module.End (O i) (Mt i)
  act_inj : ∀ i, Function.Injective (act i)
  prMt : ∀ i, what₂.MtL (mu i) (j i) →ₛₗ[embK i] TensorProduct (O i) (FractionRing (O i)) (Mt i)
  prMt_span : ∀ i, Submodule.span (FractionRing (O i)) (Set.range (prMt i)) = ⊤
  prMt_lat : ∀ i, Submodule.span (O i)
      (prMt i '' {x | what₂.jMt (mu i) (j i) x ∈ (what₂.MtLat (mu i) (j i)).gen}) =
    LinearMap.range (TensorProduct.mk (O i) (FractionRing (O i)) (Mt i) 1)
  eig_ne : ∀ i x, heckeEig (T i) (act i) x ≠ ⊥
  chi : ∀ i, ℕ → (G H.E L.nd.Om →* (O i)ˣ)
  chi_cont : ∀ i c, Continuous (fun g => ((chi i c g : (O i)ˣ) : O i))
  chi_def : ∀ i c, 1 ≤ c → c ≤ R.t → chi i c = chi i 1 *
    ((Units.map (algebraMap ℤ_[l i] (O i)).toMonoidHom).comp
      (cycZ (F := H.E) (Ω := L.nd.Om) (l i))) ^ (-((c : ℤ) - 1))
  s0 : Loc → ℕ
  restNLevelExponent_of_odd : ∀ i, l i ≠ 2 → s0 i = max 1 (H.QS.factorization (l i))
  restNLevelExponent_of_two : ∀ i, l i = 2 → s0 i = H.QS.factorization 2
  S : Loc → Finset (HeightOneSpectrum (𝓞 H.E))
  Q : Loc → Finset (HeightOneSpectrum (𝓞 H.E))
  SQ_split : ∀ i v, v ∈ S i ∨ v ∈ Q i → IsSplitPl H v
  SQ_disj : ∀ i, Disjoint (S i) (Q i)
  SQ_l : ∀ i v, v ∈ S i ∨ v ∈ Q i → v ∉ placesOver H.E (l i)
  S_def : ∀ i v, v ∈ S i ↔ (v ∈ placesOver H.E (H.g 0) ∨ v ∈ placesOver H.E (H.g 1) ∨
      v ∈ placesOver H.E (if l i = H.pde then H.pde' else H.pde)) ∧ v ∉ placesOver H.E (l i)
  hT : ∀ i, HeightOneSpectrum (𝓞 H.E) → ℕ → T i
  T_gen : ∀ i, Algebra.adjoin (O i) {f : X i → O i | ∃ v k, IsSplitPl H v ∧
      v ∉ placesOver H.E (l i) ∧ v ∉ S i ∧ v ∉ Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧ f = (hT i v k : X i → O i)} =
    T i
  gam0 : Loc → HeightOneSpectrum (𝓞 H.E) → G H.E L.nd.Om
  locNd_chebotarevPlace_mem : ∀ i v, gam0 i v ∈ Ine (F := H.E) (L.nd.plOm.1 v)
  restN_tameGenerator_generates : ∀ i v, v ∈ S i ∨ v ∈ Q i → TameGenAt (L.nd.plOm.1 v) (gam0 i v)
  chi_ram_Q : ∀ i, ∀ v ∈ Q i, ∃ g ∈ Ine (F := H.E) (L.nd.plOm.1 v), chi i 1 g ≠ 1
  Bj : Loc → Type
  [acgBj : ∀ i, AddCommGroup (Bj i)]
  [modBj : ∀ i, Module (O i) (Bj i)]
  [freeBj : ∀ i, Module.Free (O i) (Bj i)]
  [finBj : ∀ i, Module.Finite (O i) (Bj i)]

def LocNd.nd {L : NLay0 R H what₂ LL0} (X : LocNd L) : NData R H what₂ :=
  { L.nd with
    Loc := X.Loc
    l := X.l
    lPrime := X.lPrime
    j := X.j
    j_range := X.j_range
    mu := X.mu
    w := X.w
    w_l := X.w_l
    mu_w := X.mu_w
    w_tw := X.w_tw
    locs := X.locs
    locs_mem := X.locs_mem
    O := X.O
    instO := X.instO
    domO := X.domO
    dvrO := X.dvrO
    algO := X.algO
    finO := X.finO
    topO := X.topO
    trO := X.trO
    O_adic := X.O_adic
    O_complete := X.O_complete
    embK := X.embK
    embK_w := X.embK_w
    X := X.X
    finX := X.finX
    neX := X.neX
    T := X.T
    T_local := X.T_local
    T_sep := X.T_sep
    Mt := X.Mt
    acgMt := X.acgMt
    modMt := X.modMt
    freeMt := X.freeMt
    finMt := X.finMt
    act := X.act
    act_inj := X.act_inj
    prMt := X.prMt
    prMt_span := X.prMt_span
    prMt_lat := X.prMt_lat
    eig_ne := X.eig_ne
    chi := X.chi
    chi_cont := X.chi_cont
    chi_def := X.chi_def
    s0 := X.s0
    restNLevelExponent_of_odd := X.restNLevelExponent_of_odd
    restNLevelExponent_of_two := X.restNLevelExponent_of_two
    S := X.S
    Q := X.Q
    SQ_split := X.SQ_split
    SQ_disj := X.SQ_disj
    SQ_l := X.SQ_l
    S_def := X.S_def
    hT := X.hT
    T_gen := X.T_gen
    gam0 := X.gam0
    locNd_chebotarevPlace_mem := X.locNd_chebotarevPlace_mem
    restN_tameGenerator_generates := X.restN_tameGenerator_generates
    chi_ram_Q := X.chi_ram_Q
    Bj := X.Bj
    acgBj := X.acgBj
    modBj := X.modBj
    freeBj := X.freeBj
    finBj := X.finBj
    Z := fun _ => ∅
    Zgood := fun _ => ∅ }

set_option synthInstance.maxHeartbeats 400000 in

structure LocTw {L : NLay0 R H what₂ LL0} (X : LocNd L) where
  twOf : X.nd.Loc → L.ntw.Tw
  twSide : X.nd.Loc → Bool
  twOf_l : ∀ a, L.ntw.l (twOf a) = X.nd.l a
  twist₂ : ∀ a, L.ntw.O0 (twOf a) →+* X.nd.O a
  twO_emb : ∀ a (x : LL0) (y : L.ntw.O0 (twOf a)),
    algebraMap (L.ntw.O0 (twOf a)) (FractionRing (L.ntw.O0 (twOf a))) y =
      (if twSide a then L.ntw.emb0 (twOf a) else L.ntw.emb0b (twOf a)) x →
    X.nd.embK a (x : what₂.LL) = algebraMap (X.nd.O a) (FractionRing (X.nd.O a)) (twist₂ a y)
  psiL : ∀ a : X.nd.Loc, G H.E X.nd.Om →* (X.nd.O a)ˣ
  psiL_ord : ∀ a g, ∃ n : ℕ, psiL a g ^ (X.nd.l a ^ n) = 1
  psiL_open : ∀ a, IsOpen ((psiL a).ker : Set (G H.E X.nd.Om))
  psiL_anti : ∀ a, AntiHom L.ntw.cc (psiL a)
  psiL_ram : ∀ a, RamExactly (psiL a) (↑(X.nd.Q a) : Set (HeightOneSpectrum (𝓞 H.E)))
  psiL_l : ∀ a v, v ∈ placesOver H.E (X.nd.l a) → ∀ A : ValuationSubring X.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, psiL a σ = 1
  chi_tw : ∀ a, X.nd.chi a 1 =
    ((Units.map (twist₂ a).toMonoidHom).comp (L.ntw.chi1 (twOf a) (X.nd.j a) (twSide a)) : G H.E X.nd.Om →* (X.nd.O a)ˣ) * psiL a

def LocTw.ntw {L : NLay0 R H what₂ LL0} {X : LocNd L} (T : LocTw X) : NTw R H what₂ LL0 X.nd :=
  { L.ntw with
    twOf := T.twOf
    twSide := T.twSide
    twOf_l := T.twOf_l
    twist₂ := T.twist₂
    twO_emb := T.twO_emb
    psiL := T.psiL
    psiL_ord := T.psiL_ord
    psiL_open := T.psiL_open
    psiL_anti := T.psiL_anti
    psiL_ram := T.psiL_ram
    psiL_l := T.psiL_l
    chi_tw := T.chi_tw }

set_option synthInstance.maxHeartbeats 400000 in

structure LocAut {L : NLay0 R H what₂ LL0} (X : LocNd L) where
  iotaQ : ∀ i, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)
  iotaQC : ∀ i, Qbar (X.nd.l i) ≃+* ℂ
  iota_LL : ∀ i x, iotaQC i (iotaQ i (X.nd.embK i x)) = what₂.embLL x
  iotaQ_alg : ∀ i (z : ℤ_[X.nd.l i]), iotaQ i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
    (algebraMap ℤ_[X.nd.l i] (X.nd.O i) z)) = algebraMap ℚ_[X.nd.l i] (Qbar (X.nd.l i)) (z : ℚ_[X.nd.l i])
  muC : X.nd.Loc → L.naut.CG 1
  muC_csd : ∀ i, L.naut.csd (muC i)
  AV : X.nd.Loc → Type
  [finAV : ∀ i, Finite (AV i)]
  ptV : ∀ i, AV i → Option (X.nd.X i)
  typeV : ∀ i, AV i → Submodule ℂ (what₂.Mt (X.nd.mu i) (X.nd.j i))
  typeV_ne : ∀ i P, typeV i P ≠ ⊥
  typeV_indep : ∀ i, iSupIndep (typeV i)
  typeV_top : ∀ i, ⨆ P, typeV i P = ⊤
  pt_surj : ∀ i x, ∃ P, ptV i P = some x
  eig_dim : ∀ i x, X.nd.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV i P = some x}, typeV i P)
  locV : ∀ i, AV i → ∀ w, L.naut.LP w
  satV : ∀ i, AV i → PlE H → Multiset ℂ
  locV_unr : ∀ i P w, IsSplitPl H w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver H.E (H.g k)) →
    w ∉ placesOver H.E (if X.nd.l i = H.pde then H.pde' else H.pde) → L.naut.unr (locV i P w)
  pt_loc : ∀ i P x, ptV i P = some x → ∀ w, SplitOut X.nd i w →
    (heckePol X.nd i x w).map (((iotaQC i).toRingHom.comp (iotaQ i)).comp
      (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) =
    ((L.naut.frobEig (L.naut.lpTw (locV i P w) ((1 - (R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod
  infWt : X.nd.Loc → (H.E →+* ℂ) → Multiset ℂ
  locW : ∀ i : X.nd.Loc, what₂.FT → ∀ w, L.naut.LP w
  satW : ∀ i : X.nd.Loc, what₂.FT → PlE H → Multiset ℂ
  lab_loc : ∀ i k σ v, X.nd.lab k σ v = L.naut.items₂ k (L.naut.plGw k v) (locW i σ (L.naut.plGw k v))
  wdOf : ∀ i {a}, (G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) → ∀ w, L.naut.LP w
  wdOf_dim : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, L.naut.lpDim (wdOf i r w) = a
  wdOf_unr : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, w ∉ placesOver H.E (X.nd.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i)))) →
    (L.naut.unr (wdOf i r w) ↔ ∀ σ ∈ Ine (F := H.E) (X.nd.plOm.1 w), r σ = 1)
  wdOf_frob : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, w ∉ placesOver H.E (X.nd.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i)))) →
    L.naut.unr (wdOf i r w) → ∀ (B : ValuationSubring X.nd.Om) (σ : G H.E X.nd.Om), IsPlaceOver (F := H.E) B w →
    IsFrob (F := H.E) B (normV w) σ →
    ((r σ : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i))).charpoly.map
        (iotaQC i).toRingHom =
      ((L.naut.frobEig (wdOf i r w)).map fun α => Polynomial.X - Polynomial.C α).prod
  wdOf_ine : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, w ∉ placesOver H.E (X.nd.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i)))) →
    ∀ σ ∈ Ine (F := H.E) (X.nd.plOm.1 w),
    ((r σ : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i))).charpoly.map
        (iotaQC i).toRingHom = L.naut.inePol (wdOf i r w) σ
  wdOf_mono0 : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, w ∉ placesOver H.E (X.nd.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i)))) →
    (L.naut.mono0 (wdOf i r w) ↔ (r '' (Ine (F := H.E) (X.nd.plOm.1 w) : Set (G H.E X.nd.Om))).Finite)
  IsCrysW : ∀ i {a}, (G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) → PlE H → Prop
  IsPotCrysW : ∀ i {a}, (G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) → PlE H → Prop
  IsdRW : ∀ i {a}, (G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) → PlE H → Prop
  jumpsW : ∀ i {a}, (G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) → (H.E →+* Qbar (X.nd.l i)) →
    Multiset ℤ
  wdOf_unrL : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, w ∈ placesOver H.E (X.nd.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i)))) →
    IsdRW i r w → (L.naut.unr (wdOf i r w) ↔ IsCrysW i r w)
  wdOf_mono0L : ∀ i {a} (r : G H.E X.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w, w ∈ placesOver H.E (X.nd.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (X.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (X.nd.l i)))) →
    IsdRW i r w → (L.naut.mono0 (wdOf i r w) ↔ IsPotCrysW i r w)
  jumpsInf : ∀ i {a}, L.naut.CG a → (H.E →+* Qbar (X.nd.l i)) → Multiset ℤ
  locAutHodgeTateWeightsLevelZero : ∀ i, (H.E →+* Qbar (X.nd.l i)) → Multiset ℤ
  jumpsInf_def : ∀ i {a} (π : L.naut.CG a) (τ : H.E →+* Qbar (X.nd.l i)), L.naut.ralg π →
    (jumpsInf i π τ).map (fun n : ℤ => (n : ℂ)) =
      (L.naut.infG π ((iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((a : ℂ) - 1) / 2)
  locAut_hodgeTateWeightsLevelZero_def : ∀ i (τ : H.E →+* Qbar (X.nd.l i)),
    (locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) =
      (infWt i ((iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((R.nV : ℂ) - 1) / 2)
  chi_mu : ∀ i w, SplitOut X.nd i w → L.naut.unr (L.naut.locG (L.naut.tw (muC i) L.naut.etaTinv) w) ∧
    ∀ (B : ValuationSubring X.nd.Om) (σ : G H.E X.nd.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ →
      L.naut.frobEig (L.naut.lpTw (L.naut.locG (L.naut.tw (muC i) L.naut.etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
        {(iotaQC i) (iotaQ i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i)))}
  kFbar : ∀ i, IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i)

def LocAut.naut {L : NLay0 R H what₂ LL0} {X : LocNd L} (Y : LocAut X) : NAut X.nd :=
  { L.naut with
    iotaQ := Y.iotaQ
    iotaQC := Y.iotaQC
    iota_LL := Y.iota_LL
    iotaQ_alg := Y.iotaQ_alg
    muC := Y.muC
    muC_csd := Y.muC_csd
    AV := Y.AV
    finAV := Y.finAV
    ptV := Y.ptV
    typeV := Y.typeV
    typeV_ne := Y.typeV_ne
    typeV_indep := Y.typeV_indep
    typeV_top := Y.typeV_top
    pt_surj := Y.pt_surj
    eig_dim := Y.eig_dim
    locV := Y.locV
    satV := Y.satV
    locV_unr := Y.locV_unr
    pt_loc := Y.pt_loc
    infWt := Y.infWt
    locW := Y.locW
    satW := Y.satW
    lab_loc := Y.lab_loc
    wdOf := Y.wdOf
    wdOf_dim := Y.wdOf_dim
    wdOf_unr := Y.wdOf_unr
    wdOf_frob := Y.wdOf_frob
    wdOf_ine := Y.wdOf_ine
    wdOf_mono0 := Y.wdOf_mono0
    IsCrysW := Y.IsCrysW
    IsPotCrysW := Y.IsPotCrysW
    IsdRW := Y.IsdRW
    jumpsW := Y.jumpsW
    wdOf_unrL := Y.wdOf_unrL
    wdOf_mono0L := Y.wdOf_mono0L
    jumpsInf := Y.jumpsInf
    locAutHodgeTateWeightsLevelZero := Y.locAutHodgeTateWeightsLevelZero
    jumpsInf_def := Y.jumpsInf_def
    locAut_hodgeTateWeightsLevelZero_def := Y.locAut_hodgeTateWeightsLevelZero_def
    chi_mu := Y.chi_mu
    kFbar := Y.kFbar }

structure LocBC {L : NLay0 R H what₂ LL0} {X : LocNd L} (Y : LocAut X) where
  embAV : ∀ i, Y.naut.AV i → L.nbc.AU (X.nd.j i)
  embAV_inj : ∀ i, Function.Injective (embAV i)
  embAV_loc : ∀ i (P : Y.naut.AV i) w, Y.naut.locV i P w = L.nbc.locAU (X.nd.j i) (embAV i P) w
  embAV_sat : ∀ i (P : Y.naut.AV i) w, Y.naut.satV i P w = L.nbc.satAU (X.nd.j i) (embAV i P) w
  embAV_sph : ∀ i (P : Y.naut.AV i) w, ¬ IsSplitPl H w → L.nbc.sphAU (X.nd.j i) (embAV i P) w
  embAV_inf : ∀ i (P : Y.naut.AV i), Y.naut.infWt i = L.nbc.infW (X.nd.j i) (L.nbc.wtAU (X.nd.j i) (embAV i P))

def LocBC.nbc {L : NLay0 R H what₂ LL0} {X : LocNd L} {Y : LocAut X} (C : LocBC Y) : NBC Y.naut :=
  { L.nbc with
    embAV := C.embAV
    embAV_inj := C.embAV_inj
    embAV_loc := C.embAV_loc
    embAV_sat := C.embAV_sat
    embAV_sph := C.embAV_sph
    embAV_inf := C.embAV_inf }

structure LocTy {L : NLay0 R H what₂ LL0} {X : LocNd L} (Y : LocAut X) where
  bc : what₂.FT → Multiset (ℕ × ℕ)
  bc_pos : ∀ σ, ∀ p ∈ bc σ, 0 < p.1 ∧ 0 < p.2
  bc_sum : ∀ σ, ((bc σ).map (fun p => p.1 * p.2)).sum = R.r
  rbar : what₂.FT → ∀ w : what₂.places.Pl,
    G H.E X.nd.Om →* GL (Fin R.r) (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))
  rbar_open : ∀ σ w, IsOpen ((rbar σ w).ker : Set (G H.E X.nd.Om))
  heckeLoc_gamma_places : ∀ i k v, X.nd.gam0 i (Y.naut.plGw k v) = L.ntypes.tg k v
  chiT_tg : ∀ i k v, X.nd.l i ≠ H.g k →
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    (Y.naut.iotaQC i (Y.naut.iotaQ i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
        ((X.nd.chi i 1 (L.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i))) =
      L.ntypes.teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k))
        ((X.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ : (ZMod (H.g k))ˣ) : ZMod (H.g k)))) ∨
    (Y.naut.iotaQC i (Y.naut.iotaQ i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
        ((X.nd.chi i 1 (L.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i))) =
      L.ntypes.teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k))
        (((X.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹ : (ZMod (H.g k))ˣ) : ZMod (H.g k))))
  MtPar : ∀ μ j, L.ntypes.Par → Submodule ℂ (what₂.Mt μ j)

def LocTy.ntypes {L : NLay0 R H what₂ LL0} {X : LocNd L} {Y : LocAut X} (Z : LocTy Y) : NTypes Y.naut :=
  { L.ntypes with
    bc := Z.bc
    bc_pos := Z.bc_pos
    bc_sum := Z.bc_sum
    rbar := Z.rbar
    rbar_open := Z.rbar_open
    heckeLoc_gamma_places := Z.heckeLoc_gamma_places
    chiT_tg := Z.chiT_tg
    MtPar := Z.MtPar }

structure LocBr {L : NLay0 R H what₂ LL0} {X : LocNd L} (Y : LocAut X) where
  nbr : ∀ (i : X.nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (X.nd.l i) →
    Formalism.BasicNotions.LocBridge (X.nd.l i) H.E X.nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (X.nd.plOm.1 w)) (X.nd.O i)
  nbr_ind : ∀ (i : X.nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (X.nd.l i))
    (x : X.nd.Om), x ∈ X.nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : X.nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (X.nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef H.condN (nbr i w hw).LL
  loc_tie : Formalism.MainNotions.N.LocTie X.nd Y.naut L.loc nbr

structure LocAll (L : NLay0 R H what₂ LL0) where
  X : LocNd L
  T : LocTw X
  Y : LocAut X
  C : LocBC Y
  Z : LocTy Y
  B : LocBr Y
  bc_tie : Formalism.MainNotions.N.BcTie X.nd Y.naut Z.ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie X.nd Y.naut Z.ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie X.nd Y.naut Z.ntypes

set_option maxHeartbeats 2000000 in

def LocAll.lay {L : NLay0 R H what₂ LL0} (A : LocAll L) : NLay0 R H what₂ LL0 :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := A.X.nd, ntw := A.T.ntw, naut := A.Y.naut, nbc := A.C.nbc
    nexp := { L.nexp with }, ntypes := A.Z.ntypes, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq, nth := { L.nth with }
    nbr := A.B.nbr, nbr_ind := A.B.nbr_ind, self_good := A.B.self_good, ntwbr := L.ntwbr, ntwbr_ind := L.ntwbr_ind
    loc_tie := A.B.loc_tie, bc_tie := A.bc_tie, rbar_tie := A.rbar_tie, mtpar_tie := A.mtpar_tie }

end GlobalTheory.HeightCounting

end
