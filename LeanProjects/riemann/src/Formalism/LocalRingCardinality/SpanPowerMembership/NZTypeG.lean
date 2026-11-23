import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {R : Ranks} (H : Host R)

set_option synthInstance.maxHeartbeats 400000 in

def ndL (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NData R H what₂ where
  Om := AlgC
  plOm := ⟨fun v => placeOf AlgC v, fun v => isPlaceOver_placeOf AlgC v⟩
  ldat p _ := toyLocalData H p
  sha_eq := fun p _ e h1 h2 n hn => by
    rw [h.hsha p e h1 h2, hn]
    simp
  Loc := Empty
  l i := i.elim
  lPrime i := i.elim
  j i := i.elim
  j_range i := i.elim
  mu i := i.elim
  w i := i.elim
  w_l i := i.elim
  mu_w i := i.elim
  w_tw i := i.elim
  locs _ _ := ∅
  locs_mem _ _ i := i.elim
  O i := i.elim
  instO i := i.elim
  domO i := i.elim
  dvrO i := i.elim
  algO i := i.elim
  finO i := i.elim
  topO i := i.elim
  trO i := i.elim
  O_adic i := i.elim
  O_complete i := i.elim
  embK i := i.elim
  embK_w i := i.elim
  X i := i.elim
  finX i := i.elim
  neX i := i.elim
  T i := i.elim
  T_local i := i.elim
  T_sep i := i.elim
  Mt i := i.elim
  acgMt i := i.elim
  modMt i := i.elim
  freeMt i := i.elim
  finMt i := i.elim
  act i := i.elim
  act_inj i := i.elim
  prMt i := i.elim
  prMt_span i := i.elim
  prMt_lat i := i.elim
  eig_ne i := i.elim
  chi i := i.elim
  chi_cont i := i.elim
  chi_def i := i.elim
  Z i := i.elim
  Zgood i := i.elim
  s0 i := i.elim
  restNLevelExponent_of_odd i := i.elim
  restNLevelExponent_of_two i := i.elim
  S i := i.elim
  Q i := i.elim
  SQ_disj i := i.elim
  SQ_l i := i.elim
  S_def i := i.elim
  hT i := i.elim
  T_gen i := i.elim
  gam0 i := i.elim
  locNd_chebotarevPlace_mem i := i.elim
  chi_ram_Q i := i.elim
  Bj i := i.elim
  acgBj i := i.elim
  modBj i := i.elim
  freeBj i := i.elim
  finBj i := i.elim
  g_split := h.hg
  PlG _ := Fin R.f
  card_PlG _ := Fintype.card_fin _
  lab := lab
  lab_monic := hlab
  chiT _ _ _ := 1
  restN_card_levelGroup_eq := h.hcard
  SQ_split i := i.elim
  restN_tameGenerator_generates i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def ntwL {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) :
    NTw R H what₂ LL0 (ndL H what₂ h lab hlab) where
  cc := conjAlgC
  cc_cm := isCMConjOm_conjAlgC H
  Tw := Empty
  O_l i := i.elim
  topO i := i.elim
  trO i := i.elim
  O_adic i := i.elim
  delta_open i := i.elim
  twistCharacterFamily_unramified i := i.elim
  twistCharacterFamily_at_auxiliaryPlaces i := i.elim
  twistCharacterFamily_tame i := i.elim
  hk_zero i := i.elim
  jL_range i := i.elim
  lamG i := i.elim
  lamG_cont i := i.elim
  lamG_unr i := i.elim
  lamG_pD i := i.elim
  lamG_anti i := i.elim
  Xv_def i := i.elim
  qs_conj i := i.elim
  twOf i := i.elim
  twSide i := i.elim
  twOf_l i := i.elim
  twist₂ i := i.elim
  twO_emb i := i.elim
  psiL i := i.elim
  psiL_ord i := i.elim
  psiL_open i := i.elim
  psiL_anti i := i.elim
  psiL_ram i := i.elim
  psiL_l i := i.elim
  chi_tw i := i.elim
  art_univ i := i.elim
  l i := i.elim
  lPrime i := i.elim
  O0 i := i.elim
  crO0 i := i.elim
  twistBaseCoefficientRing_isDomain i := i.elim
  twistBaseCoefficientRing_isDVR i := i.elim
  algO0 i := i.elim
  twistBaseCoefficientRing_finite_padic i := i.elim
  twistBaseCoefficientRing_residueField_finite i := i.elim
  topO0 i := i.elim
  twistBaseCoefficientRing_topologicalRing i := i.elim
  twistBaseCoefficientRing_isAdic i := i.elim
  emb0 i := i.elim
  emb0b i := i.elim
  restX_coefficientEmbedding_conj i := i.elim
  O i := i.elim
  crO i := i.elim
  domO i := i.elim
  dvrO i := i.elim
  algO i := i.elim
  O_inj i := i.elim
  resO_ac i := i.elim
  O_complete i := i.elim
  Ok i := i.elim
  crOk i := i.elim
  domOk i := i.elim
  dvrOk i := i.elim
  algOk i := i.elim
  Ok_inj i := i.elim
  Ok_fin i := i.elim
  zk i := i.elim
  zk_prim i := i.elim
  Ok_gen i := i.elim
  pD i := i.elim
  pD_eq i := i.elim
  delta i := i.elim
  delta_anti i := i.elim
  delta_ram i := i.elim
  delta_15 i := i.elim
  delta_tame i := i.elim
  chi1 i := i.elim
  twistCharacterFamily_continuous i := i.elim
  Sig i := i.elim
  finSig i := i.elim
  jS i := i.elim
  jS_range i := i.elim
  side i := i.elim
  rhoS i := i.elim
  rhoS_cont i := i.elim
  S0 i := i.elim
  twistExcludedPlaces_contains_residueChar i := i.elim
  placesOver_subset_exceptional i := i.elim
  primes_subset_exceptional i := i.elim
  B i := i.elim
  acgB i := i.elim
  modB i := i.elim
  freeB i := i.elim
  finB i := i.elim
  Theta i := i.elim
  ThetaPsi i := i.elim
  ThetaPsi_one i := i.elim
  hk i := i.elim
  hEig i := i.elim
  abelian₂ i := i.elim
  finLam i := i.elim
  jL i := i.elim
  sideL i := i.elim
  s2 i := i.elim
  Xv i := i.elim
  qs i := i.elim
  qs_sq i := i.elim
  RCG i := i.elim
  grpRCG i := i.elim
  finRCG i := i.elim
  RCG_l i := i.elim
  art i := i.elim
  art_surj i := i.elim
  art_cont i := i.elim
  art_anti i := i.elim
  art_unr i := i.elim
  res i := i.elim
  res_art i := i.elim
  th i := i.elim

open Polynomial in
set_option synthInstance.maxHeartbeats 400000 in

def nautL (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NAut (ndL H what₂ h lab hlab) where
  iotaQ i := i.elim
  iotaQC i := i.elim
  iota_LL i := i.elim
  iotaQ_alg i := i.elim
  locV_unr i := i.elim
  LP _ := Multiset ℂˣ
  lpDim := fun a => Multiset.card a
  lpZero _ := 0
  lpSum := fun a b => a + b
  lpTw := fun {w} a s => a.map (· * qPow H w s)
  lpChar := fun a χ => a.map (· * χ.prod)
  lpUnr _ m := m.map toU
  mono0 := fun _ => True
  unr := fun _ => True
  frobEig := fun a => a.map Units.val
  tempered := fun a => ∀ α ∈ a.map Units.val, ‖α‖ = 1
  tempered_unr _ _ := Iff.rfl
  lpDim_char _ _ _ := Multiset.card_map _ _
  unr_char _ _ _ _ _ := trivial
  monomial_char_iff _ _ _ := Iff.rfl
  inePol := fun a _ => (X - 1) ^ Multiset.card a
  items₂ _ _ _ := 1
  lpDim_zero _ := rfl
  lpDim_sum a b := Multiset.card_add a b
  lpDim_tw a s := Multiset.card_map _ _
  lpUnr_spec _ m hm := ⟨trivial, by
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl (fun z hz => val_toU (fun h0 => hm (h0 ▸ hz)))).trans (Multiset.map_id' m),
    Multiset.card_map _ _⟩
  unr_sum _ _ := ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  monomial_sum_iff _ _ := ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  frobEig_sum a b _ _ := Multiset.map_add _ a b
  unr_tw _ _ := Iff.rfl
  monomial_twist_iff _ _ := Iff.rfl
  frobEig_tw a s _ := by rw [Multiset.map_map, Multiset.map_map]; rfl
  frobEig_char a χ c _ _ _ hχ := by
    obtain ⟨u, rfl, rfl⟩ := Multiset.map_eq_singleton.mp hχ
    rw [Multiset.map_map, Multiset.map_map, Multiset.prod_singleton]; rfl
  lpZero_unr _ := trivial
  frobEig_zero _ := rfl
  lpSum_zero a := add_zero a
  lpSum_comm a b := add_comm a b
  lpSum_assoc a b c := add_assoc a b c
  lpTw_zero a := by simp [qPow_zero]
  lpTw_add a s t := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun z _ => by simp only [Function.comp, mul_assoc, qPow_add])
  lpTw_sum a b s := Multiset.map_add _ a b
  unr_eq_lpUnr a _ := by
    rw [Multiset.map_map]
    exact ((Multiset.map_congr rfl (fun z _ => toU_val z)).trans (Multiset.map_id' a)).symm
  unr_mono0 _ _ := trivial
  frobEig_ne_zero a _ := fun h0 => by
    obtain ⟨u, -, hu⟩ := Multiset.mem_map.mp h0
    exact u.ne_zero hu
  frobEig_card a _ := Multiset.card_map _ _
  inePol_sum a b _ := by rw [Multiset.card_add, pow_add]
  inePol_tw a s _ _ := by rw [Multiset.card_map]
  unr_iff_ine _ := ⟨fun _ => ⟨trivial, fun _ _ => rfl⟩, fun _ => trivial⟩
  inertiaCharpoly_zero _ _ := rfl
  inertiaCharpoly_add _ _ _ _ := (one_mul 1).symm
  CG a := {f : PlE H → Multiset ℂˣ // ∀ w, Multiset.card (f w) = a}
  csd := fun π => ∀ w w', IsConjPl H w w' → π.1 w' = (π.1 w).map (·⁻¹)
  csd_unr := fun π w w' h hc _ => ⟨trivial, by
    rw [h w w' hc, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => Units.val_inv_eq_inv_val u)⟩
  csd_tw := fun π χ hχ hπ w w' hc => by
    show (π.1 w').map (· * (χ.1 w').prod) = ((π.1 w).map (· * (χ.1 w).prod)).map (·⁻¹)
    rw [hπ w w' hc, hχ w w' hc, Multiset.prod_map_inv', Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => (mul_inv u _).symm)
  ralg := fun {a} _ => ∀ _ : H.E →+* ℂ, (Multiset.replicate a (0 : ℂ)).Nodup ∧
    ∀ z ∈ Multiset.replicate a (0 : ℂ), ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  ralg_def := fun _ => Iff.rfl
  locG := fun π w => π.1 w
  locG_dim := fun π w => π.2 w
  locG_unr_ae := fun _ => Filter.Eventually.of_forall fun _ => trivial
  tw := fun π χ => ⟨fun w => (π.1 w).map (· * (χ.1 w).prod), fun w => (Multiset.card_map _ _).trans (π.2 w)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun {a} _ _ => Multiset.replicate a 0
  infG_tw := fun _ _ _ s hs => by
    rw [Multiset.replicate_one, Multiset.singleton_inj] at hs
    simp [← hs]
  infG_card := fun _ _ => Multiset.card_replicate _ _
  muC i := i.elim
  etaT := ⟨fun _ => {-1}, fun _ => rfl⟩
  etaTinv := ⟨fun _ => {-1}, fun _ => rfl⟩
  etaT_unr _ := trivial
  etaT_inert _ _ := by simp
  etaTinv_def _ := ⟨trivial, by simp⟩
  etaT_split _ _ _ _ a b ha hb := by
    simp only [Multiset.map_singleton, Multiset.singleton_inj, Units.val_neg, Units.val_one] at ha hb
    rw [← ha, ← hb]; norm_num
  muC_csd i := i.elim
  lab_loc i := i.elim
  wdOf_dim i := i.elim
  wdOf_unr i := i.elim
  wdOf_frob i := i.elim
  wdOf_ine i := i.elim
  wdOf_mono0 i := i.elim
  jumpsInf_def i := i.elim
  locAut_hodgeTateWeightsLevelZero_def i := i.elim
  chi_mu i := i.elim
  AV i := i.elim
  finAV i := i.elim
  ptV i := i.elim
  typeV i := i.elim
  typeV_ne i := i.elim
  typeV_indep i := i.elim
  typeV_top i := i.elim
  pt_surj i := i.elim
  eig_dim i := i.elim
  locV i := i.elim
  satV i := i.elim
  pt_loc i := i.elim
  infWt i := i.elim
  locW i := i.elim
  satW i := i.elim
  plGw k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose
  plGw_over k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.1
  plGw_inj k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.2.1
  plGw_nconj k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.2.2
  wdOf i := i.elim
  IsCrysW i := i.elim
  IsPotCrysW i := i.elim
  IsdRW i := i.elim
  jumpsW i := i.elim
  wdOf_unrL i := i.elim
  wdOf_mono0L i := i.elim
  jumpsInf i := i.elim
  locAutHodgeTateWeightsLevelZero i := i.elim
  kFbar i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def nbcL (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NBC (nautL H what₂ h lab hlab) where
  AU _ := Empty
  multAU _ π := π.elim
  sphAU _ π := π.elim
  locAU _ π := π.elim
  satAU _ π := π.elim
  satAU_card _ π := π.elim
  Wt _ := Empty
  infW _ W := W.elim
  infW_card _ W := W.elim
  infW_alg _ W := W.elim
  wtAU _ π := π.elim
  embAV i := i.elim
  embAV_inj i := i.elim
  embAV_loc i := i.elim
  embAV_sat i := i.elim
  embAV_sph i := i.elim
  embAV_inf i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def nexpL {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r)
    (eL : G0g (ndL H what₂ h lab hlab) → LL0) :
    NExp R H what₂ LL0 (ndL H what₂ h lab hlab) (ntwL H LL0 h lab hlab) where
  Fm i := i.elim
  eLL0 := eL
  eAlg_def i := i.elim
  thPsi_one i := i.elim
  twPsi_one i := i.elim
  eH i := i.elim
  eH_idem i := i.elim
  MtLat_fg i := i.elim
  MtLat_span i := i.elim
  embB i := i.elim
  embB_inj i := i.elim
  acgFm i := i.elim
  modFmK i := i.elim
  modFmO i := i.elim
  towFm i := i.elim
  fdFm i := i.elim
  actG i := i.elim
  U := ⊥
  psiU i := i.elim
  eAlg i := i.elim
  eAlg_idem i := i.elim
  eAlg_central i := i.elim
  Bsup i := i.elim
  Dat i := i.elim
  th i := i.elim
  lev i := i.elim
  thPsi i := i.elim
  thU i := i.elim
  twPsi i := i.elim
  twDel i := i.elim
  delU i := i.elim
  delU_unr i := i.elim
  delU_l i := i.elim
  delU_anti i := i.elim
  delU_open i := i.elim
  delU_res i := i.elim
  delU_conj i := i.elim
  MtV i := i.elim
  acgMt i := i.elim
  modMtK i := i.elim
  modMtO i := i.elim
  towMt i := i.elim
  fdMt i := i.elim
  MtLat i := i.elim
  thP i := i.elim
  hkF i := i.elim

theorem l_Z_tie (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) :
    ∀ i x, x ∈ (ndL H what₂ h lab hlab).Z i ↔ x ∈ Formalism.MainNotions.N.ZN (ndL H what₂ h lab hlab) (nautL H what₂ h lab hlab) i :=
  fun i => i.elim

theorem l_Zgood_tie (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) :
    ∀ i x, x ∈ (ndL H what₂ h lab hlab).Zgood i ↔
      x ∈ Formalism.MainNotions.N.ZgoodN (ndL H what₂ h lab hlab) (nautL H what₂ h lab hlab) i :=
  fun i => i.elim

theorem l_etaJ_tie (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) (hη : ∀ j w, what₂.etaJ j w = 0) :
    ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ (ndL H what₂ h lab hlab).locs j w, (ndL H what₂ h lab hlab).etaLoc i := by
  intro j w _ _
  rw [hη]
  rfl

variable {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r)
    (eL : G0g (ndL H what₂ h lab hlab) → LL0)

set_option synthInstance.maxHeartbeats 400000 in

def nthL : NTh R H what₂ LL0 (ndL H what₂ h lab hlab) (ntwL H LL0 h lab hlab) (nexpL H LL0 h lab hlab eL) where
  iC := fun i => i.elim
  iC_int := fun i => i.elim
  aL := fun i => i.elim
  aL_g := fun i => i.elim
  aL_off := fun i => i.elim
  Pt := fun i => i.elim
  ev := fun i => i.elim
  ev_smul := fun i => i.elim
  ev_inj := fun i => i.elim
  Lt := fun i => i.elim
  acgLt := fun i => i.elim
  modLt := fun i => i.elim
  freeLt := fun i => i.elim
  finLt := fun i => i.elim
  Let := fun i => i.elim
  finLet := fun i => i.elim
  Harm := fun i => i.elim
  thV := fun i => i.elim
  datPhi := fun i => i.elim
  datP := fun i => i.elim
  recDet := fun i => i.elim
  Ctr := fun i => i.elim
  ctrC := fun i => i.elim
  Harm_def := fun i => i.elim
  thV_add := fun i => i.elim
  thV_smul := fun i => i.elim
  thV_addP := fun i => i.elim
  thV_smulP := fun i => i.elim
  actK_one := fun i => i.elim
  actK_mul := fun i => i.elim
  recDet_act := fun i => i.elim
  recDetq_act := fun i => i.elim
  hkIdx := fun i => i.elim
  finHk := fun i => i.elim
  hkMove := fun i => i.elim
  hkU := fun i => i.elim
  hk_ev := fun i => i.elim
  MaximalUnramifiedExtension := fun i => i.elim
  FmUr := fun i => i.elim
  FmUr_smul := fun i => i.elim
  FmUr_span := fun i => i.elim
  Bsup_def := fun i => i.elim
  Kq := fun i => i.elim
  grpKq := fun i => i.elim
  actK := fun i => i.elim
  recDetq := fun i => i.elim
  recDetq_mem := fun i => i.elim

end Formalism.BasicNotions.Examples₂.NZ
