import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.DataKap

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure ClsPkg : Type 1 where
  cls : ℕ → Type
  clsFin : ∀ i, Fintype (cls i)
  stab : ∀ i, cls i → Type
  stabGrp : ∀ i c, Group (stab i c)
  stabFin : ∀ i c, Finite (stab i c)
  DGam : ℕ
  DGam_pos : 0 < DGam
  dvd : ∀ i c, Nat.card (stab i c) ∣ DGam

section FormsY

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
  {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [hE : ∀ i, IsEmpty (C.Y i)]
  (A : ColumnsAtT R C) (P : PeriodMap R C)

def formsY : MemberForms LL embLL Pl Tau hc C A P where
  lv := fun i v _ => Fin (R.N i) → A.Fv v
  lv_rank := fun i v _ => Module.finrank_fin_fun (A.Fv v)
  fv := fun i v _ => LinearMap.proj ⟨0, R.N_pos i⟩
  fv_ne := fun i v _ h => one_ne_zero (α := A.Fv v) (LinearMap.congr_fun h 1)
  up := fun _ _ c _ => c
  upT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  lk := fun i v _ => Fin (R.N i) → A.Fv v
  lk_rank := fun i v _ => Module.finrank_fin_fun (A.Fv v)
  te := fun i v _ => Pi.single ⟨0, R.N_pos i⟩ 1
  te_ne := fun i v _ h => by simpa using congrFun h ⟨0, R.N_pos i⟩
  dn := fun _ _ c _ => c
  dnT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil := fun _ _ _ c => c
  dilT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil_one := fun _ _ _ => rfl
  dil_mul := fun _ _ _ _ _ => rfl
  dil_fv := fun i v a _ => ⟨LinearEquiv.smulOfUnit a⁻¹, LinearMap.ext fun x => by
    show x ⟨0, R.N_pos i⟩ = (a : A.Fv v) * (((a⁻¹ : (A.Fv v)ˣ) : A.Fv v) * x ⟨0, R.N_pos i⟩)
    rw [Units.mul_inv_cancel_left]⟩
  dil_stab := fun _ _ _ _ => rfl
  rhoT_dil := fun _ _ _ _ => Subsingleton.elim _ _
  tauOf := fun _ => Fintype.equivOfCardEq (by rw [A.card_vT, hTau])
  seenP := fun _ => true
  lam := fun j τ => lamOf (hc τ) j
  lam_eq := fun j hj τ i => lamOf_eq (hc τ) j hj i
  sg := fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  Fi := fun _ => ⊥
  Fi_zero := Subsingleton.elim _ _
  ipV := fun _ _ => 0
  lat := fun _ => fmZeroHLat LL
  lat_good := fun _ => fmZeroHLat_good LL
  emb := fun _ => 0
  emb_basis := fun _ => ⟨linearIndependent_empty_type, by
    rw [Set.range_eq_empty, Submodule.span_empty]⟩
  emb_norm := fun i x => by
    rw [fmZeroHLat_maj]
    simp
  rhoT_lat := fun _ _ _ _ => ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩
  Bw := fun _ _ _ => ⊤
  Bw_span := fun _ _ _ => Subsingleton.elim _ _
  clsP := Empty
  stabilizer₂ := fun _ => Unit
  til := fun c => c.elim
  stabMap := fun c => c.elim
  stabMap_inj := fun c => c.elim
  evz_til := fun φ ψ _ => by rw [Subsingleton.elim φ ψ]
  ptC := ⊥
  ipP := 0
  ptLat := fmZeroHLat LL
  ptLat_good := fmZeroHLat_good LL
  ptEmb := 0
  ptEmb_basis := ⟨linearIndependent_empty_type, by rw [Set.range_eq_empty, Submodule.span_empty]⟩
  ptEmb_norm := fun x => by
    rw [fmZeroHLat_maj]
    simp
  beOn := fun _ => 0
  beOn_nonneg := fun _ => le_rfl
  thFree := fun _ _ _ _ => 0
  thFree_nonneg := fun _ _ _ _ => le_rfl

end FormsY

section Member3

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg)

abbrev chain3 : ColumnChain R Tau hc where
  cls := K.cls
  clsFin := K.clsFin
  stab := K.stab
  stabGrp := K.stabGrp
  stabFin := K.stabFin
  DGam := K.DGam
  DGam_pos := K.DGam_pos
  dvd_DGam := fun i _ c => K.dvd i c
  Y := fun _ => Empty
  de := fun _ y => y.elim
  de_ne := fun _ y => y.elim
  rhoDet := fun _ _ => 1
  rhoDet' := fun _ _ => 1
  rho_norm := fun _ _ _ => norm_one
  rho'_norm := fun _ _ _ => norm_one
  unf := fun _ _ _ => 0
  sSharp := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h τ => by rw [dif_pos h]; exact (sInt R (hc τ) ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h τ => by rw [dif_pos h]; exact (sInt R (hc τ) ⟨i, h⟩).1.choose_spec.symm

instance (i : ℕ) : IsEmpty ((chain3 hc K).Y i) := ⟨fun c => Empty.elim c⟩

variable (T : ℕ) [hT : Fact T.Prime]

abbrev classLevelColumnsAt (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chain3 hc K) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := du
    duStar_pos := hdu
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

instance (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) :
    Subsingleton (classLevelColumnsAt hc K T Dst hD du hdu Gam hG).Mram :=
  ⟨fun _ _ => Subtype.ext (funext fun _ => funext fun y => Empty.elim y)⟩

abbrev period3 : PeriodMap R (chain3 hc K) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

abbrev mem3 (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) : Member R Tau hc :=
  ⟨chain3 hc K, classLevelColumnsAt hc K T Dst hD du hdu Gam hG, period3 hc K⟩

end Member3

abbrev div3 (F : Type) [Field F] [NumberField F] [StarRing F] (etaF hv : ℝ) : DivData F Unit :=
  { toyZeroLatticeDatum F with
    etaF := etaF
    h := fun _ => hv
    HH := sFrame (fun _ : Unit => zeroHLat F) (fun _ => hv) + (zeroHLat F).muMax
    HH_ge := le_refl _ }

section Record

variable {R : Ranks} (H : Host R)

abbrev classLevelData (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ) : Rows.Data R :=
  { rowsG H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) Dst (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H) with kaBig := kb, kaSmall := ks }

theorem nHyp3 (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (classLevelData H Dst kb ks) where
  hsha := fun p _ e _ _ => shaExample_eq H p e
  hcard := rfl
  hg := hg

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def classRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H T pz hpz
    what₂ := classLevelData H Dst kb ks
    eTau := Equiv.refl _
    hc := hc
    wordFin := inferInstanceAs (Fintype Unit)
    u₀ := ()
    hcW := fun _ => hc
    hcW_base := rfl
    hcW_v := fun _ _ => rfl
    hcW_b := fun _ _ => rfl
    hcW_e := fun _ _ => rfl
    hcW_first := fun _ _ _ => rfl
    hcW_last := fun _ _ _ => rfl
    mem := fun _ => mem3 hc K T Dst hD du hdu Gam hG
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := div3 H.E etaF hv
    div_good := ⟨(zeroHLat_good H.E).1, fun _ => (zeroHLat_good H.E).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := fun _ => hlev
    T_norm := fun _ => ⟨pz, hK, hpz, hcong⟩
    sp_T := rfl
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by rw [map_one, one_mul, one_mul]
    T_win := fun _ => hwin
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ => lat
    clsLat_lat := fun _ => hlat
    eMu := fun _ => LinearEquiv.ofSubsingleton Z0 (mem3 hc K T Dst hD du hdu Gam hG).A.Mram
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (mem3 hc K T Dst hD du hdu Gam hG).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (mem3 hc K T Dst hD du hdu Gam hG).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := vol
    vol_pos := hvol
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero H.E H.φ₀
    jEE_basis := jZero_basis H.E H.φ₀
    jN := fun _ => jZero H.E H.φ₀
    jN_basis := fun _ => jZero_basis H.E H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl (Tau2 R))
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl (Tau2 R))
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl (Tau2 R)) N L L')
    relDet_self := fun N L => congrArg QuotientGroup.mk (relDetExample_self H (Equiv.refl (Tau2 R)) N L)
    relDet_mul := fun N L L' L'' =>
      congrArg QuotientGroup.mk (relDetExample_mul H (Equiv.refl (Tau2 R)) N L L' L'')
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl (Tau2 R)) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ _ => by simp
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ _ _ => by simp
    dsig := dsg
    dsig_pos := hdsg
    s := sData2 H hc Del hDel hgap hlet cdS hcdS hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := Module.finrank_zero_of_subsingleton (R := ℂ) (M := Z0)
    s_Cu := fun _ => LinearEquiv.ofSubsingleton Z0 (mem3 hc K T Dst hD du hdu Gam hG).A.Mu0
    s_PlF := Equiv.refl _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (classLevelData H Dst kb ks) (nHyp3 H Dst kb ks hg)
    ntw := ntwToy H ⊤ (nHyp3 H Dst kb ks hg)
    naut := nautToy H (classLevelData H Dst kb ks) (nHyp3 H Dst kb ks hg)
    nbc := nbcToy H (classLevelData H Dst kb ks) (nHyp3 H Dst kb ks hg)
    nexp := nexpToy H ⊤ (nHyp3 H Dst kb ks hg)
    ntypes := ntypesT H (classLevelData H Dst kb ks) (nHyp3 H Dst kb ks hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (classLevelData H Dst kb ks) (nHyp3 H Dst kb ks hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHyp3 H Dst kb ks hg)
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero H.φ₀).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun _ => formsY H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) (mem3 hc K T Dst hD du hdu Gam hG).C (mem3 hc K T Dst hD du hdu Gam hG).A (mem3 hc K T Dst hD du hdu Gam hG).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_eq_zero fun _ _ => mul_zero _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun _ => funext fun y => Empty.elim y
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_eq_zero fun _ _ => mul_zero _).symm
    cd := G.cd
    jet := jetToy R H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := fun _ _ _ => gAtPExample _
    gat_d := fun _ _ _ => (gAtPExample_d _).trans (finrank_bot ℂ _).symm
    Y_sigval := spaces_signature_eq R _ _ _ _ _ _ _ }

theorem classRecord_host :
    (⟨(classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).R, (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).host⟩ : Σ R : Ranks, Host R) = ⟨R, H⟩ := rfl
theorem classRecord_ranks :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).R = R := rfl
theorem classRecord_word (u : (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).what₂.Word) :
    u = (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).u₀ := rfl
theorem classRecord_sign :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).hc = hc := rfl
theorem classRecord_weight_sign (u) :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).hcW u = hc := rfl
theorem classRecord_eta (j w) :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).what₂.etaJ j w = 0 := rfl
theorem classRecord_mem_A_T (u) :
    ((classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).mem u).A.T = T := rfl
theorem classRecord_gamma (u) :
    ((classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).mem u).A.GamP = Gam := rfl
theorem classRecord_discriminantLevel (u) :
    ((classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).mem u).A.duStar = du := rfl
theorem classRecord_dimensionBound :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).what₂.Dstar = Dst := rfl
theorem classRecord_delta :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).s.Del = Del := rfl
theorem classRecord_letter (u l) :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).s.letter u l = false := rfl
theorem classRecord_cdScale :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).s.cdScale = cdS := rfl
theorem classRecord_dsig :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).dsig = dsg := rfl
theorem classRecord_etaF :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).div.etaF = etaF := rfl
theorem classRecord_height (u) :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).div.h u = hv := rfl
theorem classRecord_volume :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).vol = vol := rfl
theorem classRecord_rowDimension_zero :
    (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).what₂.Drows = 0 := rfl
theorem classRecord_lowerLevel (u) : ((classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks).mem u).A.Tstar =
    (Dst / du) ^ ((1 : ℝ) / (R.f * R.k)) * Gam ^ (-(2 : ℝ) / (R.f * R.k)) := rfl

omit kb ks in

theorem classRecord_weights_defined : ∃ kb ks, DV.KapDef (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks) := by
  obtain ⟨kb, ks, h⟩ := DV.exists_blocks (classRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G (fun _ _ _ => 0) (fun _ _ _ => 0))
  exact ⟨kb, ks, fun j _ _ τ => h j τ⟩

end Record

end Formalism.BasicNotions.Examples₂
