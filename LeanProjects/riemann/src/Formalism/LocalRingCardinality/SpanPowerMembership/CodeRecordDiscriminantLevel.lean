import Formalism.LocalRingCardinality.SpanPowerMembership.TwistRecordRowDimensionZero

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

section Rows5

variable {R : Ranks} (W : Type) (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)

abbrev primaryLevelData : Rows.Data R where
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
  Word := W
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

end Rows5

abbrev div5 (F : Type) [Field F] [NumberField F] [StarRing F] (W : Type) [Fintype W] (etaF : ℝ) (hv : W → ℝ) :
    DivData F W where
  RR := zeroHLat F
  Nu := fun _ => zeroHLat F
  Bk := fun _ => 0
  h := hv
  HH := sFrame (fun _ : W => zeroHLat F) hv + (zeroHLat F).muMax
  HH_ge := le_refl _
  etaF := etaF
  Dall := 0
  delP := 0
  delP_le_one := zero_le_one

section Record

variable {R : Ranks} (H : Host R)

theorem pz_ne {T : ℕ} [hT : Fact T.Prime] {z : H.E} (h : z * H.conj z = (T : H.E)) : z ≠ 0 := by
  rintro rfl
  exact hT.out.ne_zero (by exact_mod_cast (zero_mul _).symm.trans h |>.symm)

theorem norm_quotient_mul_conj {T T' : ℕ} [Fact T'.Prime] {z z' : H.E} (h : z * H.conj z = (T : H.E))
    (h' : z' * H.conj z' = (T' : H.E)) : z / z' * H.conj (z / z') * (T' : H.E) = (T : H.E) := by
  have h1 := pz_ne H h'
  have h2 : H.conj z' ≠ 0 := (map_ne_zero H.conj).mpr h1
  rw [map_div₀, ← h, ← h']
  field_simp

abbrev codeLevelData (W : Type) (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w) : Rows.Data R :=
  primaryLevelData W H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) Dst (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H) kb ks tw htw

theorem nHyp5 (W : Type) (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (codeLevelData H W Dst kb ks tw htw) where
  hsha := fun p _ e _ _ => shaExample_eq H p e
  hcard := rfl
  hg := hg

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

abbrev sData5 (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R H.F H.E (conjF H) W (Tau2 R) hcW where
  cdScale := cdS
  cdScale_pos := hcdS
  Del := Del
  Del_pos := hDel
  cloud_gap := hgap
  letter := lt
  letter_inj := hlt
  u_letter := hlet
  HH := EuclideanSpace ℂ (Fin 0)
  Cu := fun _ => EuclideanSpace ℂ (Fin 0)
  Pu := fun _ => 0
  volN := fun _ => 1
  volH := fun _ => 1
  volN_pos := fun _ => one_pos
  volH_pos := fun _ => one_pos
  Term := fun _ _ => Empty
  aTerm := fun _ _ t => t.elim
  isId := fun _ => False
  inS := fun _ => False
  relevant := fun _ => False
  FeqF := fun _ => False
  Gterm := fun t => t.elim
  atP := locAdj (conjF H) {H.g 0, H.g 1} (slocH H) (fun p hp => (splH H hg ht.jac p hp).some)
  PlF := HeightOneSpectrum (𝓞 H.F)
  BBne := fun _ _ => False
  generic := fun _ => False
  Pair := fun _ _ => Empty
  pfst := fun t => t.elim
  psnd := fun t => t.elim
  s0 := fun _ => 0
  scalarPair := fun _ => False
  pval := fun _ => 0
  ptOf := fun t => t.elim
  cTerm := fun _ => 0
  massPair := fun _ => 0
  meanCount := fun _ _ _ => 0

abbrev memW (K : W → ClsPkg) (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ)
    (hdu : ∀ u, 0 < du u) (Gam : ℝ) (hG : 1 < Gam) (u : W) : Member R (Tau2 R) (hcW u) :=
  mem3 (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def codeRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)
    what₂ := codeLevelData H W Dst kb ks tw htw
    eTau := Equiv.refl _
    hc := hcW u0
    wordFin := inferInstanceAs (Fintype W)
    u₀ := u0
    hcW := hcW
    hcW_base := rfl
    hcW_v := hv0
    hcW_b := hb0
    hcW_e := he0
    hcW_first := hf0
    hcW_last := hl0
    mem := fun u => memW hcW K T Dst hD du hdu Gam hG u
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := div5 H.E W etaF hv
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
    T_level := hlev
    T_norm := fun u => ⟨pz u, hK u, hpz u, hcong u⟩
    sp_T := rfl
    cOf := fun u => (pz u0 : H.E) / (pz u : H.E)
    cOf_ne := fun u => div_ne_zero (pz_ne H (hpz u0)) (pz_ne H (hpz u))
    cOf_eq := fun u => norm_quotient_mul_conj H (hpz u0) (hpz u)
    T_win := hwin
    GamP_eq := fun _ => rfl
    T_ne_pde := hpde
    Dstar_eq := fun _ => rfl
    clsLat := lat
    clsLat_lat := hlat
    eMu := fun u => LinearEquiv.ofSubsingleton Z0 (memW hcW K T Dst hD du hdu Gam hG u).A.Mram
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun u _ => (memW hcW K T Dst hD du hdu Gam hG u).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun u _ => (memW hcW K T Dst hD du hdu Gam hG u).P
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
    s := sData5 H hcW Del hDel hgap lt hlt hlet cdS hcdS hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := Module.finrank_zero_of_subsingleton (R := ℂ) (M := Z0)
    s_Cu := fun u => LinearEquiv.ofSubsingleton Z0 (memW hcW K T Dst hD du hdu Gam hG u).A.Mu0
    s_PlF := Equiv.refl _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (codeLevelData H W Dst kb ks tw htw) (nHyp5 H W Dst kb ks tw htw hg)
    ntw := ntwToy H ⊤ (nHyp5 H W Dst kb ks tw htw hg)
    naut := nautToy H (codeLevelData H W Dst kb ks tw htw) (nHyp5 H W Dst kb ks tw htw hg)
    nbc := nbcToy H (codeLevelData H W Dst kb ks tw htw) (nHyp5 H W Dst kb ks tw htw hg)
    nexp := nexpToy H ⊤ (nHyp5 H W Dst kb ks tw htw hg)
    ntypes := ntypesT H (codeLevelData H W Dst kb ks tw htw) (nHyp5 H W Dst kb ks tw htw hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (codeLevelData H W Dst kb ks tw htw) (nHyp5 H W Dst kb ks tw htw hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHyp5 H W Dst kb ks tw htw hg)
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
    fm := fun u => formsY H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) (memW hcW K T Dst hD du hdu Gam hG u).C (memW hcW K T Dst hD du hdu Gam hG u).A (memW hcW K T Dst hD du hdu Gam hG u).P
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

theorem codeRecord_ranks :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).R = R := rfl
theorem codeRecord_wordType :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Word = W := rfl
theorem codeRecord_weight_sign :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).hcW = hcW := rfl
theorem codeRecord_letter :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).s.letter = lt := rfl
theorem codeRecord_delta :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).s.Del = Del := rfl
theorem codeRecord_height :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.h = hv := rfl
theorem codeRecord_dimensionBound :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Dstar = Dst := rfl
theorem codeRecord_twistAt :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.muAt = tw := rfl
theorem codeRecord_volume :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).vol = vol := rfl
theorem codeRecord_dsig :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).dsig = dsg := rfl
theorem codeRecord_cdScale :
    (codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).s.cdScale = cdS := rfl
theorem codeRecord_mem_A_T (u) : ((codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.T = T u := rfl
theorem codeRecord_discriminantLevel (u) : ((codeRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.duStar = du u := rfl

end Record

def hcLet {R : Ranks} (h : HCParam R) (n : ℕ) (a : Fin (R.k - 2) → Bool) : Fin R.k → ℚ := fun i =>
  if hi : 1 ≤ i.1 ∧ i.1 - 1 < R.k - 2 then h.u i - (if a ⟨i.1 - 1, hi.2⟩ then (n : ℚ) else 0) else h.u i

section Words

variable {R : Ranks} (h : HCParam R) (n : ℕ)
  (hgap : ∀ (l : ℕ) (hl : l + 1 < R.k - 1), h.v ⟨l, by omega⟩ - h.v ⟨l + 1, hl⟩ = 4 * (n : ℚ))
  (hlet : ∀ (l : ℕ) (hl : l < R.k - 2), h.u ⟨l + 1, by omega⟩ = h.v ⟨l, by omega⟩ - 1 / 2)
  (hn : 0 < n) (a : Fin (R.k - 2) → Bool)

theorem hcLet_mid (l : ℕ) (hl : l < R.k - 2) :
    hcLet h n a ⟨l + 1, by omega⟩ = h.u ⟨l + 1, by omega⟩ - (if a ⟨l, hl⟩ then (n : ℚ) else 0) := by
  unfold hcLet
  rw [dif_pos ⟨by simp, by simpa using hl⟩]
  rfl

theorem hcLet_end (i : Fin R.k) (hi : i.1 = 0 ∨ R.k - 2 ≤ i.1 - 1) : hcLet h n a i = h.u i := by
  unfold hcLet
  rw [dif_neg (by omega)]

def hcWord : HCParam R :=
  { h with
    u := hcLet h n a
    u_gt_v := fun i => by
      obtain ⟨i, hi⟩ := i
      rcases i with _ | l
      · rw [hcLet_end h n a _ (Or.inl rfl)]; exact h.u_gt_v ⟨0, hi⟩
      · have hl : l < R.k - 2 := by omega
        have h1 := hgap l hi
        have h2 : (1 : ℚ) ≤ n := by exact_mod_cast hn
        show h.v ⟨l + 1, hi⟩ < hcLet h n a ⟨l + 1, _⟩
        rw [hcLet_mid h n a l hl, hlet l hl]
        split_ifs <;> linarith
    v_gt_u := fun i => by
      have h1 := h.v_gt_u i
      have h2 : (0 : ℚ) ≤ n := by positivity
      unfold hcLet
      split_ifs <;> linarith
    u_last_gt := fun h0 h' => by
      rw [hcLet_end h n a _ (Or.inr (by show R.k - 2 ≤ R.k - 1 - 1; omega))]; exact h.u_last_gt h0 h'
    u_half := fun i => by
      obtain ⟨z, hz⟩ := h.u_half i
      unfold hcLet
      split_ifs
      · exact ⟨z - n, by rw [hz]; push_cast; ring⟩
      · exact ⟨z, by rw [hz]; ring⟩
      · exact ⟨z, hz⟩ }

theorem hcWord_letter (l : ℕ) (hl : l < R.k - 2) :
    (hcWord h n hgap hlet hn a).u ⟨l + 1, by omega⟩ =
      (hcWord h n hgap hlet hn a).v ⟨l, by omega⟩ - 1 / 2 - (if a ⟨l, hl⟩ then (n : ℚ) else 0) := by
  show hcLet h n a ⟨l + 1, _⟩ = h.v ⟨l, _⟩ - 1 / 2 - _
  rw [hcLet_mid h n a l hl, hlet l hl]

end Words

theorem card_word_le (D : D7) : Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 2) := by
  simpa using Fintype.card_le_of_injective _ D.s.letter_inj

theorem del_int_of_low (D : D7) (u : D.what₂.Word) (l : Fin (D.R.k - 2)) (h : D.s.letter u l = true)
    (τ : D.what₂.Tau) : ∃ z : ℤ, D.s.Del = z := by
  have h1 := D.s.u_letter u τ l.1 l.2
  obtain ⟨a, ha⟩ := (D.hcW u τ).u_half ⟨l.1 + 1, by omega⟩
  obtain ⟨b, hb⟩ := (D.hcW u τ).v_int ⟨l.1, by omega⟩
  rw [ha, hb, show D.s.letter u ⟨l.1, l.2⟩ = true from h, if_pos rfl] at h1
  exact ⟨b - a - 1, by push_cast; linarith⟩

end Formalism.BasicNotions.Examples₂
