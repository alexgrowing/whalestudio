import Formalism.LocalRingCardinality.SpanPowerMembership.CodeRecordDiscriminantLevel
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColH
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowD
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

def padConj {d n : ℕ} (h : d ≤ n) : En d →ₗᵢ⋆[ℂ] En n where
  toFun x := WithLp.toLp 2 fun i => if hi : (i : ℕ) < d then starRingEnd ℂ (x ⟨i, hi⟩) else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < d <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < d <;> simp [hi]
  norm_map' x := by
    show ‖WithLp.toLp 2 fun i : Fin n => if hi : (i : ℕ) < d then starRingEnd ℂ (x ⟨i, hi⟩) else 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun i hi => ?_)
      (fun k => ?_)).symm
    · have : ¬ (i : ℕ) < d := fun hlt => hi ⟨⟨i, hlt⟩, rfl⟩
      simp [this]
    · simp

section Chain

theorem chainOpM_add {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (f g : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (f + g) = Formalism.ThetaLiftIndependence.chainOpM w Km m f + Formalism.ThetaLiftIndependence.chainOpM w Km m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext j
    simp only [Formalism.ThetaLiftIndependence.kerOpM, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

theorem chainOpM_smul {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext j
    simp only [Formalism.ThetaLiftIndependence.kerOpM, Pi.smul_apply, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact smul_comm _ _ _

theorem col_add {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (f g : C.cls 0 → C.Y 0 → ℂ) : C.col (f + g) = C.col f + C.col g := chainOpM_add C.wt C.Kmap R.m f g

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) : C.col (c • f) = c • C.col f := chainOpM_smul C.wt C.Kmap R.m c f

end Chain

abbrev divN (F : Type) [Field F] [NumberField F] [StarRing F] {W : Type} [Fintype W] (K : W → ClsPkg) (etaF : ℝ)
    (hv : W → ℝ) (d Dall : ℕ) (NuL : ∀ u : W, Submodule (𝓞 F) ((K u).cls 0 → F)) : DivData F W where
  RR := stdH F d
  Nu := fun u => { stdHLat F ((K u).cls 0) with L := NuL u }
  Bk := fun _ => 0
  h := hv
  HH := sFrame (fun u : W => { stdHLat F ((K u).cls 0) with L := NuL u }) hv + (stdH F d).muMax
  HH_ge := le_refl _
  etaF := etaF
  Dall := Dall
  delP := 1 - (d : ℝ) / Dall
  delP_le_one := by
    have : (0 : ℝ) ≤ (d : ℝ) / Dall := by positivity
    linarith

section Record

variable {R : Ranks} (H : Host R)

section Per

variable {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (d : ℕ)
  (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)

def perN (u : W) (μ : Bool) (φ : MuN ((K u).cls 0)) (F : En d) : ℂ :=
  (periodN (hcW u) (K u) (En d) (per u μ)).PtilCol (eE _ φ) F

theorem perN_linL (u : W) (μ : Bool) (F : En d) : IsLinearMap ℂ (fun φ => perN hcW K d per u μ φ F) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_add, col_add, map_add, map_add, map_add, LinearMap.add_apply]
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_smul, col_smul, map_smul, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem perN_linR (u : W) (μ : Bool) (φ : MuN ((K u).cls 0)) : IsLinearMap ℂ (fun F => perN hcW K d per u μ φ F) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_add]
  · unfold perN Formalism.BasicNotions.PeriodMap.PtilCol Formalism.BasicNotions.PeriodMap.Ptil
    rw [map_smul, smul_eq_mul]

end Per

abbrev rowsHN {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
    (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)
    (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)
    (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ) : Rows.Data R :=
  rowsN H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) Dst (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H) kb ks tw htw W (fun u => (K u).cls 0) d Dall d0 hd FT ft ft0
    (perN hcW K d per) (fun _ _ => 0) (fun _ _ => le_refl _)

theorem nHypN {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (Dst : ℝ)
    (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
    (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
    (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)
    (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)
    (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) where
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

abbrev sDataN (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) (K : W → ClsPkg)
    (Dall : ℕ) : Formalism.MainNotions.S.Draft.SData R H.F H.E (conjF H) W (Tau2 R) hcW :=
  { sData5 H hcW Del hDel hgap lt hlt hlet cdS hcdS hg ht with
    HH := En Dall
    hhN := inferInstance
    hhI := inferInstance
    hhF := inferInstance
    Cu := fun u => MuN ((K u).cls 0)
    cuN := fun _ => inferInstance
    cuI := fun _ => inferInstance
    cuF := fun _ => inferInstance
    Pu := fun _ => 0
    aTerm := fun _ _ t => t.elim }

abbrev memC (K : W → ClsPkg) (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ)
    (hdu : ∀ u, 0 < du u) (Gam : ℝ) (hG : 1 < Gam) (d : ℕ)
    (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ) (u : W) : Member R (Tau2 R) (hcW u) :=
  ⟨chainN (hcW u) (K u), atTN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG,
    periodN (hcW u) (K u) (En d) (per u false)⟩

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

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def hostLevelRecord : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R
    host := H
    sp := hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)
    what₂ := rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per
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
    mem := fun u => memC hcW K T Dst hD du hdu Gam hG d per u
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := divN H.E K etaF hv d Dall NuL
    div_good := ⟨stdH_frames H.E d, fun u => (stdHLat_good H.E ((K u).cls 0)).1⟩
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
    eMu := fun u => eMuN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (hT2 u)
    eMt := fun _ => LinearEquiv.refl ℂ (En d)
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun u F => perN_linL hcW K d per u false F
    Bu_linR := fun u φ => perN_linR hcW K d per u false φ
    chTw := fun u _ => (memC hcW K T Dst hD du hdu Gam hG d per u).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun u μ => periodN (hcW u) (K u) (En d) (per u μ)
    eMtTw := fun _ _ => LinearEquiv.refl ℂ (En d)
    perCol_tie := fun _ _ _ _ _ => rfl
    vol := vol
    vol_pos := hvol
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jB H.φ₀ (eb d)
    jEE_basis := jB_basis H.φ₀ (eb d)
    jN := fun _ => jE H.φ₀
    jN_basis := fun _ => jE_basis H.φ₀
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
    s := sDataN H hcW Del hDel hgap lt hlt hlet cdS hcdS hg ht K Dall
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := finrank_euclideanSpace_fin
    s_Cu := fun u => eCuN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG
    s_PlF := Equiv.refl _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndG H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg)
    ntw := ntwL H ⊤ (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
    naut := nautL H (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
    nbc := nbcL H (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
    nexp := nexpL H ⊤ (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb)
      (fun g => ((qcL H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) g : ℚ) : ↥(⊤ : IntermediateField ℚ H.E)))
    ntypes := ntypesL H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ht G.tame
    nStage_trivialCharacter_compat := ntypesL_E0Tie H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ht G.tame (fun _ => rfl) (fun _ _ => rfl)
    nth := nthL H ⊤ (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) (labL Lb) (labL_monic Lb) _
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
    nStage_trivialCharacter_coeff_eq := fun g => labelIdempotent_baseField H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ⊤ ht G.tame g
    Z_tie := l_Z_tie H _ _ _ _
    Zgood_tie := l_Zgood_tie H _ _ _ _
    etaJ_tie := l_etaJ_tie H _ _ _ _ (fun _ _ => rfl)
    fm := fun u => formsN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R)
    eMu_isom := fun u φ ψ => (inner_eE _ φ ψ).trans
      (formsN_ipC (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) 0 _ _).symm
    nuIn := fun _ => LinearMap.id
    nuIn_inj := fun _ => Function.injective_id
    nuIn_range := fun u => LinearMap.range_id.trans
      (formsN_ramSub (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) (hT2 u)).symm
    nuIn_jN := fun _ x => eE_jE H.φ₀ x
    nuIn_norm := fun _ _ _ => rfl
    jEE_norm := jB_norm H.φ₀ (eb d)
    sEE := padConj hd
    s_Cu_isom := fun u φ ψ => (inner_eE _ φ ψ).trans
      (formsN_ipC (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u false) H.φ₀ (placesOf H.E) (card_realPlaces_eq_degree R) 0 _ _).symm
    cd := G.cd
    jet := jetToy R H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := gat
    gat_d := fun u w h => (hgat u w h).trans (atTN_rank (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG).symm
    Y_sigval := spaces_signature_eq R _ _ _ _ _ _ _ }

end Record

end Formalism.BasicNotions.Examples₂.NZ
