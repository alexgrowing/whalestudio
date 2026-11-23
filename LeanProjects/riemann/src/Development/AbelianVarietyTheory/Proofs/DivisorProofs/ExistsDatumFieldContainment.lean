import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.CodeRecordDiscriminantLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

noncomputable section

namespace GlobalTheory.FieldEnlarge

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

def noClasses : ClsPkg where
  cls := fun _ => Empty
  clsFin := fun _ => inferInstance
  stab := fun _ c => c.elim
  stabGrp := fun _ c => c.elim
  stabFin := fun _ c => c.elim
  DGam := 1
  DGam_pos := one_pos
  dvd := fun _ c => c.elim

section Record

variable {R : Ranks} (H : Host R) (L : Type) [Field L] [NumberField L] [StarRing L] (e : L →+* ℂ)

abbrev rowsOver (W : Type) (Dst : ℝ) : Rows.Data R :=
  primaryLevelData W L e (placesOf L) (Tau2 R) (card_realPlaces_eq_degree R) Dst (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false)
    (fun _ => rfl)

theorem rowsOver_hyp (W : Type) (Dst : ℝ)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsOver H L e W Dst) where
  hsha := fun p _ n _ _ => shaExample_eq H p n
  hcard := rfl
  hg := hg

variable [IsTotallyComplex L] [IsGalois ℚ L] (hstar : ∀ x : L, e (star x) = starRingEnd ℂ (e x))
  (j : H.E →+* L) (hj : e.comp j = H.φ₀)

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
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def recordOver : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)
    what₂ := rowsOver H L e W Dst
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
    mem := fun u => memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u
    nfLL := inferInstanceAs (NumberField L)
    starLL := inferInstanceAs (StarRing L)
    tcLL := inferInstanceAs (IsTotallyComplex L)
    galLL := inferInstanceAs (IsGalois ℚ L)
    starLL_cx := hstar
    div := div5 L W 0 (fun _ => 0)
    div_good := ⟨(zeroHLat_good L).1, fun _ => (zeroHLat_good L).1⟩
    embE := j
    embE_φ₀ := hj
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => e.injective (by
      rw [hstar, ← RingHom.comp_apply e j, ← RingHom.comp_apply e j, hj]; exact baseEmbedding_conj H x)
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨RingOfIntegers.mapRingHom j x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq L
    ram_eq := placesOf_ram_eq L
    conj_val := placesOf_conj_val L
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
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun u => LinearEquiv.ofSubsingleton Z0 (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).A.Mram
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun u _ => (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun u _ => (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ _ _ _ => rfl
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero L e
    jEE_basis := jZero_basis L e
    jN := fun _ => jZero L e
    jN_basis := fun _ => jZero_basis L e
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
    dsig := fun _ => 1
    dsig_pos := fun _ => one_pos
    s := sData5 H hcW Del hDel hgap lt hlt hlet cdS hcdS hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := Module.finrank_zero_of_subsingleton (R := ℂ) (M := Z0)
    s_Cu := fun u => LinearEquiv.ofSubsingleton Z0 (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).A.Mu0
    s_PlF := Equiv.refl _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (rowsOver H L e W Dst) (rowsOver_hyp H L e W Dst hg)
    ntw := ntwToy H ⊤ (rowsOver_hyp H L e W Dst hg)
    naut := nautToy H (rowsOver H L e W Dst) (rowsOver_hyp H L e W Dst hg)
    nbc := nbcToy H (rowsOver H L e W Dst) (rowsOver_hyp H L e W Dst hg)
    nexp := nexpToy H ⊤ (rowsOver_hyp H L e W Dst hg)
    ntypes := ntypesT H (rowsOver H L e W Dst) (rowsOver_hyp H L e W Dst hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (rowsOver H L e W Dst) (rowsOver_hyp H L e W Dst hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (rowsOver_hyp H L e W Dst hg)
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
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero e).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun u => formsY e (placesOf L) (card_realPlaces_eq_degree R) (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).C (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).A (memW hcW (fun _ => noClasses) T Dst hD du hdu Gam hG u).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_eq_zero fun _ _ => mul_zero _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → L) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule L (Fin 0 → L)) _ _
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

end Record

theorem typePrimes (D : D7) : THyp D.host where
  cond := D.ntypes.g_cond
  bb := D.ntypes.BB_disj
  jac := fun k => by
    have h := D.ntypes.g_cond k
    have h4 : D.host.g k % (4 * D.host.d) = 1 % (4 * D.host.d) := by
      have hd : 4 * D.host.d ∣ D.host.QS * D.host.q * D.host.d :=
        Nat.mul_dvd_mul ((dvd_trans ⟨2 ^ D.R.e, by ring⟩ D.host.tower_dvd : 4 ∣ D.host.QS).mul_right _) dvd_rfl
      rw [← Nat.mod_mod_of_dvd _ hd, h]
    have h2 : D.host.g k % 2 = 1 := by
      have hd : 2 ∣ D.host.QS * D.host.q * D.host.d :=
        (((by norm_num : 2 ∣ 4).trans (dvd_trans ⟨2 ^ D.R.e, by ring⟩ D.host.tower_dvd : 4 ∣ D.host.QS)).mul_right _).mul_right _
      rw [← Nat.mod_mod_of_dvd _ hd, h]
    refine ⟨by omega, ?_⟩
    rw [jacobiSym.mod_right _ (Nat.odd_iff.mpr h2), Int.natAbs_neg, Int.natAbs_natCast, h4]
    have := jacobiSym.mod_right (-(D.host.d : ℤ)) (odd_one (α := ℕ))
    rw [Int.natAbs_neg, Int.natAbs_natCast] at this
    rw [← this, jacobiSym.one_right]

theorem exists_record_over (D : D7) (L : Type) [Field L] [NumberField L] [StarRing L] (e : L →+* ℂ)
    [IsTotallyComplex L] [IsGalois ℚ L] (hstar : ∀ x : L, e (star x) = starRingEnd ℂ (e x))
    (j : D.host.E →+* L) (hj : e.comp j = D.host.φ₀) :
    ∃ D' : D7, D'.R = D.R ∧ HEq D'.host D.host ∧ GlobalTheory.ShFam.fieldLL D' = e.toRatAlgHom.fieldRange := by
  haveI : ∀ u, Fact ((D.mem u).A.T).Prime := fun u => ⟨(D.mem u).A.T_prime⟩
  choose pz hK hpz hcong using D.T_norm
  refine ⟨recordOver D.host L e hstar j hj D.u₀ (fun u τ => D.hcW u (D.eTau.symm τ))
    (fun u τ => (D.hcW_v u _).trans (D.hcW_v _ _).symm) (fun u τ => (D.hcW_b u _).trans (D.hcW_b _ _).symm)
    (fun u τ => (D.hcW_e u _).trans (D.hcW_e _ _).symm)
    (fun u τ h => (D.hcW_first u _ h).trans (D.hcW_first _ _ h).symm)
    (fun u τ h => (D.hcW_last u _ h).trans (D.hcW_last _ _ h).symm)
    D.s.Del D.s.Del_pos (fun u τ l h => D.s.cloud_gap u _ l h) D.s.letter D.s.letter_inj
    (fun u τ l h => D.s.u_letter u _ l h) D.s.cdScale D.s.cdScale_pos
    (fun u => (D.mem u).A.T) D.what₂.Dstar (D.Dstar_eq D.u₀ ▸ (D.mem D.u₀).A.Dstar_pos)
    (fun u => (D.mem u).A.duStar) (fun u => (D.mem u).A.duStar_pos) (D.mem D.u₀).A.GamP (D.mem D.u₀).A.one_lt_gammaP
    (fun u => ?_) D.nd.g_split (typePrimes D) D.T_level D.T_ne_pde pz hK hpz hcong (LocalGap.localGapOfRecord D D.host),
    rfl, HEq.rfl, rfl⟩
  have h := D.T_win u
  simp only [ColumnsAtT.Tstar, ColumnsAtT.Xu] at h ⊢
  rw [D.Dstar_eq u, D.GamP_eq u] at h
  exact h

@[reducible] def conjStar (L : IntermediateField ℚ ℂ) [Normal ℚ L] : StarRing L where
  star := fun x => (starRingEnd ℂ).toRatAlgHom.restrictNormal L x
  star_involutive := fun x => Subtype.ext (by
    have h := fun y : L => (starRingEnd ℂ).toRatAlgHom.restrictNormal_commutes L y
    exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _)))
  star_mul := fun x y => by
    show (starRingEnd ℂ).toRatAlgHom.restrictNormal L (x * y) = _
    rw [map_mul, mul_comm]
  star_add := fun x y => map_add ((starRingEnd ℂ).toRatAlgHom.restrictNormal L) x y

theorem exists_record_ge (D : D7) (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K) :
    ∃ D' : D7, D'.R = D.R ∧ HEq D'.host D.host ∧ K ⊔ GlobalTheory.ShFam.fieldLL D ≤ GlobalTheory.ShFam.fieldLL D' := by
  haveI : FiniteDimensional ℚ (GlobalTheory.ShFam.fieldLL D) :=
    (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv.finiteDimensional
  let M : IntermediateField ℚ ℂ := K ⊔ GlobalTheory.ShFam.fieldLL D
  haveI : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_sup _ _
  let L : IntermediateField ℚ ℂ := IntermediateField.normalClosure ℚ M ℂ
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ M ℂ
  haveI : IsNormalClosure ℚ M L :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  haveI : Normal ℚ L := IsNormalClosure.normal (K := M)
  haveI : NumberField L := {}
  haveI : IsGalois ℚ L := {}
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hmem : ∀ x, D.what₂.embLL x ∈ L := fun x => hML (le_sup_right (a := K) ⟨x, rfl⟩)
  let i : D.what₂.LL →+* L := D.what₂.embLL.codRestrict L.toSubfield hmem
  haveI : IsTotallyComplex L := by
    letI : Algebra D.what₂.LL L := i.toAlgebra
    exact isTotallyComplex_of_algebra D.what₂.LL L
  letI : StarRing L := conjStar L
  obtain ⟨D', h1, h2, h3⟩ := exists_record_over D L (algebraMap L ℂ)
    (fun x => (starRingEnd ℂ).toRatAlgHom.restrictNormal_commutes L x) (i.comp D.embE) D.embE_φ₀
  refine ⟨D', h1, h2, ?_⟩
  rw [h3]
  exact fun x hx => ⟨⟨x, hML hx⟩, rfl⟩

theorem exists_record_le_fieldLL (D : D7) (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K) :
    ∃ D' : D7, D'.R = D.R ∧ HEq D'.host D.host ∧ K ≤ GlobalTheory.ShFam.fieldLL D' := by
  obtain ⟨D', h1, h2, h3⟩ := exists_record_ge D K hK
  exact ⟨D', h1, h2, le_sup_left.trans h3⟩

end GlobalTheory.FieldEnlarge
