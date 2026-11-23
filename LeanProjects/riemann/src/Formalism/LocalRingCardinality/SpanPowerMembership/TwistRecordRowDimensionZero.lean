import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

section Rows4

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)

abbrev secondaryLevelData : Rows.Data R where
  LL := LL
  embLL := embLL
  places := P
  O := 𝓞 LL
  OtoLL := algebraMap (𝓞 LL) LL
  Tau := Tau
  card_Tau := hTau
  Tup := Bool
  mu0 := false
  muStar := true
  muStar' := true
  muAt := tw
  muAt_conj := htw
  muTw := fun _ => true
  muTw_conj := fun _ => rfl
  muAt_or := fun w => Bool.eq_false_or_eq_true (tw w) |>.symm
  EE := Z0
  Drows := 0
  onb := EuclideanSpace.basisFun (Fin 0) ℂ
  Dall := 0
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Z0
  D0 := 0
  onb0 := EuclideanSpace.basisFun (Fin 0) ℂ
  FT := Empty
  ft := fun i => i.elim0
  ft0 := fun i => i.elim0
  Dstar := Dst
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => LinearIsometryEquiv.refl ℂ Z0
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => zeroOLat _
  eOp := fun _ => 0
  eOp_idem := fun _ => by simp
  eOp_sa := fun _ => LinearMap.IsSymmetric.zero
  restRowsFiniteGroupCard := cg
  restRowsFiniteGroupCard_pos := hcg
  Word := Unit
  Mu := fun _ => Z0
  perCol := fun _ _ _ _ => 0
  Bu := fun _ _ _ => 0
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  Mj := fun _ => Z0
  MjLat := fun _ => zeroOLat _
  kaBig := kb
  kaSmall := ks
  Mt := fun _ _ => Z0
  MtLat := fun _ _ => zeroOLat _
  MtL := fun _ _ => PUnit
  jMt := fun _ _ => 0
  jMt_basis := by
    intro μ j b
    have : IsEmpty (Module.Free.ChooseBasisIndex LL PUnit) :=
      ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
    exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩
  MtLat_sub := fun _ _ x hx => by simp [zeroOLat] at hx
  eMt := fun _ _ => 0
  eMt_idem := fun _ _ => by simp
  eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
  eMt_LL := fun _ _ _ => ⟨0, by simp⟩
  thetaP := fun _ _ => 0
  isot := fun _ i => i.elim
  lamP := fun _ _ _ => 0
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0
  etaJ := fun _ _ => 0
  etaJ_nonneg := fun _ _ => le_refl _
  shaLen := sha
  shaLen_nonneg := hsha

end Rows4

section Record

variable {R : Ranks} (H : Host R)

abbrev twistLevelData (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w) : Rows.Data R :=
  secondaryLevelData H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) Dst (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H) kb ks tw htw

theorem nHyp4 (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (twistLevelData H Dst kb ks tw htw) where
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
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def twistRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H T pz hpz
    what₂ := twistLevelData H Dst kb ks tw htw
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
    perCol_tie := fun _ _ _ _ _ => rfl
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
    nd := ndToy H (twistLevelData H Dst kb ks tw htw) (nHyp4 H Dst kb ks tw htw hg)
    ntw := ntwToy H ⊤ (nHyp4 H Dst kb ks tw htw hg)
    naut := nautToy H (twistLevelData H Dst kb ks tw htw) (nHyp4 H Dst kb ks tw htw hg)
    nbc := nbcToy H (twistLevelData H Dst kb ks tw htw) (nHyp4 H Dst kb ks tw htw hg)
    nexp := nexpToy H ⊤ (nHyp4 H Dst kb ks tw htw hg)
    ntypes := ntypesT H (twistLevelData H Dst kb ks tw htw) (nHyp4 H Dst kb ks tw htw hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (twistLevelData H Dst kb ks tw htw) (nHyp4 H Dst kb ks tw htw hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHyp4 H Dst kb ks tw htw hg)
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

theorem twistRecord_host :
    (⟨(twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).R, (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).host⟩ : Σ R : Ranks, Host R) = ⟨R, H⟩ := rfl
theorem twistRecord_ranks :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).R = R := rfl
theorem twistRecord_word (u : (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Word) :
    u = (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).u₀ := rfl
theorem twistRecord_sign :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).hc = hc := rfl
theorem twistRecord_weight_sign (u) :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).hcW u = hc := rfl
theorem twistRecord_eta (j w) :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.etaJ j w = 0 := rfl
theorem twistRecord_mem_A_T (u) :
    ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.T = T := rfl
theorem twistRecord_gamma (u) :
    ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.GamP = Gam := rfl
theorem twistRecord_discriminantLevel (u) :
    ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.duStar = du := rfl
theorem twistRecord_dimensionBound :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Dstar = Dst := rfl
theorem twistRecord_delta :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).s.Del = Del := rfl
theorem twistRecord_letter (u l) :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).s.letter u l = false := rfl
theorem twistRecord_cdScale :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).s.cdScale = cdS := rfl
theorem twistRecord_dsig :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).dsig = dsg := rfl
theorem twistRecord_etaF :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.etaF = etaF := rfl
theorem twistRecord_height (u) :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.h u = hv := rfl
theorem twistRecord_volume :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).vol = vol := rfl
theorem twistRecord_rowDimension_zero :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Drows = 0 := rfl
theorem twistRecord_lowerLevel (u) : ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.Tstar =
    (Dst / du) ^ ((1 : ℝ) / (R.f * R.k)) * Gam ^ (-(2 : ℝ) / (R.f * R.k)) := rfl

omit kb ks in

theorem twistRecord_weights_defined : ∃ kb ks, DV.KapDef (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := by
  obtain ⟨kb, ks, h⟩ := DV.exists_blocks (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G (fun _ _ _ => 0) (fun _ _ _ => 0) tw htw)
  exact ⟨kb, ks, fun j _ _ τ => h j τ⟩

theorem twistRecord_baseTwist :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.mu0 = false := rfl
theorem twistRecord_twistAt :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.muAt = tw := rfl
theorem twistRecord_twist_place (w) :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.muTw w = true := rfl
theorem twistRecord_coefficient_zero (j w) :
    (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Aj j w = 0 := rfl

end Record

end Formalism.BasicNotions.Examples₂
