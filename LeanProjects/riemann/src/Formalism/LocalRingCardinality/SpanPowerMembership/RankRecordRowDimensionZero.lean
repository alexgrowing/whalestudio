import Formalism.LocalRingCardinality.SpanPowerMembership.GenericMemberLevelNearLower
import Formalism.LocalRingCardinality.SpanPowerMembership.BaseFormAnisotropicOrthogonalSingle

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

abbrev Tau2 (R : Ranks) : Type := ↥(R.Psi)

theorem card_realPlaces_eq_degree (R : Ranks) : Fintype.card (Tau2 R) = R.f := by
  rw [← Nat.card_eq_fintype_card, R.toFrame.natCard_Psi]
  rfl

theorem fk_ne (R : Ranks) : R.f * R.k ≠ 0 := by
  have h1 : 0 < R.f := by unfold Ranks.f Ranks.n; positivity
  have h2 : 0 < R.k := by have := R.m_add_three_le_k; omega
  exact (Nat.mul_pos h1 h2).ne'

section Member2

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R)

abbrev chain2 : ColumnChain R Tau hc where
  cls := fun _ => Empty
  stab := fun _ c => c.elim
  stabGrp := fun _ c => c.elim
  stabFin := fun _ c => c.elim
  DGam := 1
  DGam_pos := one_pos
  dvd_DGam := fun _ _ c => c.elim
  Y := fun _ => Unit
  de := fun _ _ _ => 1
  de_ne := fun _ _ _ => one_ne_zero
  rhoDet := fun _ c => c.elim
  rhoDet' := fun _ c => c.elim
  rho_norm := fun _ _ c => c.elim
  rho'_norm := fun _ _ c => c.elim
  unf := fun _ c => c.elim
  sSharp := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h τ => by rw [dif_pos h]; exact (sInt R (hc τ) ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h τ => by rw [dif_pos h]; exact (sInt R (hc τ) ⟨i, h⟩).1.choose_spec.symm

instance (i : ℕ) : IsEmpty ((chain2 hc).cls i) := ⟨fun c => Empty.elim c⟩

variable (T : ℕ) [hT : Fact T.Prime]

abbrev levelColumnsAt (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chain2 hc) :=
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
    duStar := 1
    duStar_pos := one_pos
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

instance (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) :
    Subsingleton (levelColumnsAt hc T Dst hD Gam hG).Mram :=
  ⟨fun _ _ => Subtype.ext (funext fun c => (IsEmpty.false c).elim)⟩

abbrev period2 : PeriodMap R (chain2 hc) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

end Member2

def dstarOfRanks (R : Ranks) (Ts Gam : ℝ) : ℝ :=
  (Ts * Gam ^ ((2 : ℝ) / ((R.f * R.k : ℕ) : ℝ))) ^ (R.f * R.k)

theorem dstar2_pos (R : Ranks) {Ts Gam : ℝ} (hTs : 0 < Ts) (hG : 1 < Gam) : 0 < dstarOfRanks R Ts Gam := by
  have : 0 < Gam := by linarith
  unfold dstarOfRanks; positivity

abbrev div2 (K : Type) [Field K] [NumberField K] [StarRing K] (etaF : ℝ) : DivData K Unit :=
  { toyZeroLatticeDatum K with etaF := etaF }

section Record

variable {R : Ranks}

abbrev mem2 (hc : Tau2 R → HCParam R) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) : Member R (Tau2 R) hc :=
  ⟨chain2 hc, levelColumnsAt hc T (dstarOfRanks R Ts Gam) (dstar2_pos R hTs hG) Gam hG, period2 hc⟩

theorem rankMember_lowerLevel_eq (hc : Tau2 R → HCParam R) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) : (mem2 hc T Ts hTs Gam hG).A.Tstar = Ts := by
  have hG0 : 0 < Gam := by linarith
  show (dstarOfRanks R Ts Gam / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((R.f : ℝ) * (R.k : ℝ))) *
    Gam ^ (-(2 : ℝ) / ((R.f : ℝ) * (R.k : ℝ))) = Ts
  have hn : (R.f : ℝ) * (R.k : ℝ) = ((R.f * R.k : ℕ) : ℝ) := by push_cast; ring
  rw [Nat.cast_one, div_one, hn, one_div, dstarOfRanks,
    Real.pow_rpow_inv_natCast (by positivity) (fk_ne R), mul_assoc, ← Real.rpow_add hG0]
  rw [show (2 : ℝ) / ((R.f * R.k : ℕ) : ℝ) + -2 / ((R.f * R.k : ℕ) : ℝ) = 0 by ring, Real.rpow_zero,
    mul_one]

theorem rankMember_level_near_lower (hc : Tau2 R → HCParam R) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts) :
    (mem2 hc T Ts hTs Gam hG).A.Tstar ≤ ((mem2 hc T Ts hTs Gam hG).A.T : ℝ) ∧
      ((mem2 hc T Ts hTs Gam hG).A.T : ℝ) ≤
        (1 + 1 / ((R.f : ℝ) * R.k)) * (mem2 hc T Ts hTs Gam hG).A.Tstar := by
  rw [rankMember_lowerLevel_eq]
  exact ⟨hw1, hw2⟩

variable (H : Host R)

abbrev hostLevelData (Ts Gam : ℝ) : Rows.Data R :=
  rowsG H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) (dstarOfRanks R Ts Gam) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

theorem nHyp_hostLevelData_of_places_card (Ts Gam : ℝ)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (hostLevelData H Ts Gam) where
  hsha := fun p _ e _ _ => shaExample_eq H p e
  hcard := rfl
  hg := hg

def hostSpacesOfNorm (T : ℕ) [hT : Fact T.Prime] (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces R H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesOfRanks R star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

abbrev sData2 (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R H.F H.E (conjF H) Unit (Tau2 R) (fun _ => hc) :=
  { toySData (conjF H) (fun _ => hc) Del hDel (fun _ τ l h => hgap τ l h)
      (fun _ τ l h => hlet τ l h) (locAdj (conjF H) {H.g 0, H.g 1} (slocH H)
        (fun p hp => (splH H hg ht.jac p hp).some)) with
    cdScale := cdS
    cdScale_pos := hcdS }

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def rankRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H T pz hpz
    what₂ := hostLevelData H Ts Gam
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
    mem := fun _ => mem2 hc T Ts hTs Gam hG
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := div2 H.E etaF
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
    T_win := fun _ => rankMember_level_near_lower hc T Ts hTs Gam hG hw1 hw2
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun _ => LinearEquiv.ofSubsingleton Z0 (mem2 hc T Ts hTs Gam hG).A.Mram
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (mem2 hc T Ts hTs Gam hG).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (mem2 hc T Ts hTs Gam hG).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
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
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ c => Empty.elim c
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ i c => Empty.elim c
    dsig := dsg
    dsig_pos := hdsg
    s := sData2 H hc Del hDel hgap hlet cdS hcdS hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := Module.finrank_zero_of_subsingleton (R := ℂ) (M := Z0)
    s_Cu := fun _ => LinearEquiv.ofSubsingleton Z0 (mem2 hc T Ts hTs Gam hG).A.Mu0
    s_PlF := Equiv.refl _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (hostLevelData H Ts Gam) (nHyp_hostLevelData_of_places_card H Ts Gam hg)
    ntw := ntwToy H ⊤ (nHyp_hostLevelData_of_places_card H Ts Gam hg)
    naut := nautToy H (hostLevelData H Ts Gam) (nHyp_hostLevelData_of_places_card H Ts Gam hg)
    nbc := nbcToy H (hostLevelData H Ts Gam) (nHyp_hostLevelData_of_places_card H Ts Gam hg)
    nexp := nexpToy H ⊤ (nHyp_hostLevelData_of_places_card H Ts Gam hg)
    ntypes := ntypesT H (hostLevelData H Ts Gam) (nHyp_hostLevelData_of_places_card H Ts Gam hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (hostLevelData H Ts Gam) (nHyp_hostLevelData_of_places_card H Ts Gam hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHyp_hostLevelData_of_places_card H Ts Gam hg)
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
    fm := fun _ => formsToy H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) (mem2 hc T Ts hTs Gam hG).C (mem2 hc T Ts hTs Gam hG).A (mem2 hc T Ts hTs Gam hG).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_of_isEmpty _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun c => Empty.elim c
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_of_isEmpty _).symm
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

theorem rankRecord_host : (⟨(rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).R, (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).host⟩ : Σ R : Ranks, Host R) = ⟨R, H⟩ := rfl
theorem rankRecord_ranks : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).R = R := rfl
theorem rankRecord_word (u : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).what₂.Word) : u = (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).u₀ := rfl
theorem rankRecord_embedding (τ : Tau2 R) : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).eTau τ = τ := rfl
theorem rankRecord_hc_eq : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).hc = hc := rfl
theorem rankRecord_hcW_eq (u) : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).hcW u = hc := rfl
theorem rankRecord_eta (j w) : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).what₂.etaJ j w = 0 := rfl
theorem rankRecord_mem_A_T (u) : ((rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).mem u).A.T = T := rfl
theorem rankRecord_lowerLevel (u) : ((rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).mem u).A.Tstar = Ts := rankMember_lowerLevel_eq hc T Ts hTs Gam hG
theorem rankRecord_gamma (u) : ((rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).mem u).A.GamP = Gam := rfl
theorem rankRecord_delta : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).s.Del = Del := rfl
theorem rankRecord_letter (u l) : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).s.letter u l = false := rfl
theorem rankRecord_cdScale : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).s.cdScale = cdS := rfl
theorem rankRecord_cd : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).cd = G.cd := rfl
theorem rankRecord_dsig : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).dsig = dsg := rfl
theorem rankRecord_etaF : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).div.etaF = etaF := rfl
theorem rankRecord_dimensionBound : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).what₂.Dstar = dstarOfRanks R Ts Gam := rfl
theorem rankRecord_rowDimension_zero : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).what₂.Drows = 0 := rfl
theorem rankRecord_divisor_zero : (rankRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G).div.R = 0 := by
  show ∑ u : Unit, (zeroHLat H.E).rank = 0
  simp [zeroHLat_rank]

end Record

end Formalism.BasicNotions.Examples₂
