import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace GlobalTheory.Mem.RowsRestModel

open Formalism.BasicNotions NumberField

variable {B : Base}

abbrev Eu (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

structure Fits (C : Cols B) (d : C.Tup → ℕ) : Prop where
  mt0 : ∀ u, Nonempty ((C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0))
  mtTw : ∀ u μ, Nonempty ((C.PTw u μ).Mt ≃ₗ[ℂ] Eu (d μ))
  herm : ∀ u (x y : (C.mem u).A.Mram), starRingEnd ℂ ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y
  pos : ∀ u (x : (C.mem u).A.Mram), 0 ≤ ((C.fm u).ipC 0 x x).re
  defn : ∀ u (x : (C.mem u).A.Mram), (C.fm u).ipC 0 x x = 0 → x = 0

theorem fits_of_rows {C : Cols B} (W : RowsRest B C) : Fits C (fun μ => Module.finrank ℂ (W.Amb μ)) where
  mt0 u := ⟨(W.eMt0 u).trans (stdOrthonormalBasis ℂ (W.Amb C.mu0)).repr.toLinearEquiv⟩
  mtTw u μ := ⟨(W.eMtTw u μ).trans (stdOrthonormalBasis ℂ (W.Amb μ)).repr.toLinearEquiv⟩
  herm u x y := by
    obtain ⟨a, rfl⟩ := (W.eMu u).surjective x
    obtain ⟨b, rfl⟩ := (W.eMu u).surjective y
    rw [← W.eMu_isom, ← W.eMu_isom, inner_conj_symm]
  pos u x := by
    obtain ⟨a, rfl⟩ := (W.eMu u).surjective x
    rw [← W.eMu_isom]
    exact inner_self_nonneg (𝕜 := ℂ)
  defn u x h := by
    obtain ⟨a, rfl⟩ := (W.eMu u).surjective x
    rw [← W.eMu_isom, inner_self_eq_zero] at h
    rw [h, map_zero]

def MuT (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mram

instance (C : Cols B) (u : B.Word) : AddCommGroup (MuT C u) := inferInstanceAs (AddCommGroup (C.mem u).A.Mram)
instance (C : Cols B) (u : B.Word) : Module ℂ (MuT C u) := inferInstanceAs (Module ℂ (C.mem u).A.Mram)
instance (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (MuT C u) :=
  haveI := (C.mem u).A.Mu0_fd
  (Submodule.finiteDimensional_of_le (inf_le_left : (C.mem u).A.Mram ≤ (C.mem u).A.Mu0) :
    FiniteDimensional ℂ (C.mem u).A.Mram)

@[reducible] def core {C : Cols B} {d : C.Tup → ℕ} (h : Fits C d) (u : B.Word) : InnerProductSpace.Core ℂ (MuT C u) where
  inner x y := (C.fm u).ipC 0 (Subtype.val x) (Subtype.val y)
  conj_inner_symm x y := h.herm u x y
  re_inner_nonneg x := h.pos u x
  add_left x y z := by
    show (C.fm u).ipC 0 (x.1 + y.1) z.1 = (C.fm u).ipC 0 x.1 z.1 + (C.fm u).ipC 0 y.1 z.1
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    show (C.fm u).ipC 0 (r • x.1) y.1 = starRingEnd ℂ r * (C.fm u).ipC 0 x.1 y.1
    simp only [MemberForms.ipC, Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := h.defn u x hx

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Eu n) where
  gen := by classical exact Finset.univ.image (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  span_top := by
    classical
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Module.Basis.span_eq _

def stdJ {L : Type} [Field L] (σ : L →+* ℂ) (n : ℕ) : (Fin n → L) →ₛₗ[σ] Eu n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem stdJ_single {L : Type} [Field L] (σ : L →+* ℂ) (n : ℕ) (i : Fin n) :
    stdJ σ n (Pi.single i 1) = (EuclideanSpace.basisFun (Fin n) ℂ).toBasis i := by
  ext k
  by_cases h : k = i
  · subst h; simp [stdJ]
  · simp [stdJ, h, Pi.single_eq_of_ne h]

theorem stdJ_basis {L : Type} [Field L] (σ : L →+* ℂ) (n : ℕ) {κ : Type} (b : Module.Basis κ L (Fin n → L)) :
    LinearIndependent ℂ (fun i => stdJ σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => stdJ σ n (b i))) = ⊤ := by
  constructor
  · letI : Algebra L ℂ := σ.toAlgebra
    have h : LinearIndependent ℂ (fun i => algebraMap L ℂ ∘ b i) :=
      linearIndependent_algebraMap_comp_iff.2 b.linearIndependent
    exact h.map' (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  · have h : ∀ x, stdJ σ n x ∈ Submodule.span ℂ (Set.range (fun i => stdJ σ n (b i))) := by
      intro x
      have hx : x ∈ Submodule.span L (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← stdJ_single σ]
    exact h _

def trunc (a b : ℕ) : Eu a →ₗ[ℂ] Eu b :=
  Matrix.toEuclideanLin (Matrix.of fun (i : Fin b) (k : Fin a) => if (i : ℕ) = k then (1 : ℂ) else 0)

theorem trunc_self (a : ℕ) (x : Eu a) : trunc a a x = x := by
  have : (Matrix.of fun (i : Fin a) (k : Fin a) => if (i : ℕ) = k then (1 : ℂ) else 0) = 1 := by
    ext i k; simp [Matrix.one_apply, Fin.ext_iff]
  simp [trunc, this]

theorem chain_lin {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (j : ℕ) :
    IsLinearMap ℂ (Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j) := by
  induction j with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ j ih =>
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · show C.Klin j _ = C.Klin j _ + C.Klin j _
      rw [ih.map_add, map_add]
    · show C.Klin j _ = c • C.Klin j _
      rw [ih.map_smul, map_smul]

def mdim (n e : ℕ) : ℕ → ℕ
  | 0 => n
  | _ + 1 => e

theorem mdim_m (R : Ranks) (n e : ℕ) : mdim n e R.m = e := by
  have := R.two_le_m
  obtain ⟨k, hk⟩ : ∃ k, R.m = k + 1 := ⟨R.m - 1, by omega⟩
  rw [hk]; rfl

def model {C : Cols B} {d : C.Tup → ℕ} (h : Fits C d) (n n₀ a : ℕ) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.muStar
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Eu n
  Drows := n
  onb := EuclideanSpace.basisFun (Fin n) ℂ
  Dall := 2 * n
  delp := 1 / 2
  delp_le_one := by norm_num
  D_eq := by push_cast; ring
  EE0 := Eu n₀
  D0 := n₀
  onb0 := EuclideanSpace.basisFun (Fin n₀) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Eu (d μ)
  Mult μ j := Eu (mdim n (d μ) j)
  multZero _ := LinearIsometryEquiv.refl ℂ (Eu n)
  multTop μ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (mdim_m B.R n (d μ)))
  io μ j := trunc _ _
  Mtilde μ := stdOLat _ _ _
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ := fun _ _ => rfl
  Mu u := MuT C u
  instMu u := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core h u)
  instMui u := InnerProductSpace.ofCore (core h u).toCore
  instMuf u := inferInstanceAs (FiniteDimensional ℂ (MuT C u))
  perCol u μ φ F := by
    classical
    exact if hμ : μ = C.mu0 then (C.mem u).P.PtilCol φ.1 ((h.mt0 u).some.symm (hμ ▸ F))
      else (C.PTw u μ).PtilCol (C.e0Tw u μ φ.1) ((h.mtTw u μ).some.symm F)
  Bu u φ F := (C.mem u).P.PtilCol φ.1 ((h.mt0 u).some.symm (trunc n (d C.mu0) F))
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Eu a
  MjLat _ := stdOLat _ _ _
  kaBig _ _ _ := 1
  kaSmall _ _ _ := -1
  Mt _ _ := Eu a
  MtLat _ _ := stdOLat _ _ _
  MtL _ _ := Fin a → B.LL
  jMt _ _ := stdJ B.embLL a
  jMt_basis _ _ b := stdJ_basis _ _ b
  MtLat_sub _ _ x hx := by
    classical
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨_, stdJ_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ := fun _ _ => rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 1
  shaLen_nonneg _ _ := zero_le_one
  eMu u := LinearEquiv.refl ℂ (C.mem u).A.Mram
  eMt0 u := (h.mt0 u).some
  perCol_base_eq_PtilCol u φ F := by
    rw [dif_pos rfl]; rfl
  Bu_linL u F := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · show (C.mem u).P.Ptil (Formalism.ThetaLiftIndependence.chainOpM (C.mem u).C.wt (C.mem u).C.Kmap B.R.m (x.1 + y.1)) _ = _
      rw [(chain_lin _ _).map_add]
      simp [PeriodMap.Ptil, PeriodMap.PtilCol, ColumnChain.col]
    · show (C.mem u).P.Ptil (Formalism.ThetaLiftIndependence.chainOpM (C.mem u).C.wt (C.mem u).C.Kmap B.R.m (c • x.1)) _ = _
      rw [(chain_lin _ _).map_smul]
      simp [PeriodMap.Ptil, PeriodMap.PtilCol, ColumnChain.col]
  Bu_linR u φ := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> simp [PeriodMap.Ptil, PeriodMap.PtilCol]
  eMtTw u μ := (h.mtTw u μ).some
  perCol_tie u μ hμ φ F := by
    rw [dif_neg hμ]; rfl
  eMu_isom _ _ _ := rfl

theorem nonempty_iff (C : Cols B) : Nonempty (RowsRest B C) ↔ ∃ d, Fits C d :=
  ⟨fun ⟨W⟩ => ⟨_, fits_of_rows W⟩, fun ⟨_, h⟩ => ⟨model h 1 1 1⟩⟩

theorem two_lt_alt (B : Pre) (u : B.Word) : 2 < B.T u := by
  have h := B.level_split _ (B.T_level u)
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  have h2 : B.T u ≠ 2 := by
    intro h2
    rw [if_pos (show B.T u ∈ B.host.small from h2 ▸ B.host.two_mem_small)] at h
    cases h
  have := (B.T_prime u).two_le
  omega

open GlobalTheory.MemberTorsor in

@[reducible] def tmem (B : Base) (u : B.Word) : Member B.R (Tau B.R) (B.hcW u) := by
  classical
  exact haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    ⟨chain B.R (Tau B.R) (B.hcW u) (B.T u),
      { atT B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) with
        duStar := B.duStar u, duStar_pos := B.duStar_pos u, Dstar := B.Dstar, Dstar_pos := B.Dstar_pos,
        GamP := B.GamP, one_lt_gammaP := B.one_lt_gammaP },
      period B.R (Tau B.R) (B.hcW u) (B.T u)⟩

open GlobalTheory.MemberTorsor in

def tcols (C : Cols B) : Cols B where
  mem := tmem B
  A_T _ := rfl
  A_duStar _ := rfl
  A_Dstar _ := rfl
  A_GamP _ := rfl
  clsLat _ i _ := letI := B.host.cmStar; (B.sp.X i).L0
  clsLat_lat _ i _ := letI := B.host.cmStar; (B.sp.X i).standardTuple_isLattice
  Tup := Bool
  mu0 := false
  muStar := true
  muStar' := true
  chTw u _ := (tmem B u).C
  memberColumns_twistedChain_base _ := rfl
  e0Tw _ _ := LinearEquiv.refl ℂ _
  PTw u _ := (tmem B u).P
  Dt := C.Dt
  detCls _ _ _ := 1
  muTil := C.muTil
  chiD := C.chiD
  UO := C.UO
  chiD_UO := C.chiD_UO
  e1Dt := C.e1Dt
  rest_detCharacter_on_unitary_eq := C.rest_detCharacter_on_unitary_eq
  relDet := C.relDet
  relDet_self := C.relDet_self
  relDet_mul := C.relDet_mul
  relDet_smul := C.relDet_smul
  rhoDet_eq_inv_muTilde_chiD_pow _ _ _ := by simp
  rhoDetPrime_eq_muTilde_mul_chi_pow _ _ _ := by simp
  fm u := by
    classical
    exact haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
      { forms B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) B.LL B.embLL B.places with }

theorem tcols_ipC (C : Cols B) (u : B.Word) (x y : ((tcols C).mem u).C.cls 0 → Unit → ℂ) :
    ((tcols C).fm u).ipC 0 x y = ∑ c, starRingEnd ℂ (x c ()) * y c () := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ((tcols C).mem u).C.wt 0 c = 1 := by
    show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ = 1
    simp
  rw [this, one_mul]
  rfl

def lineEquiv : ℂ ≃ₗ[ℂ] Eu 1 := (stdOrthonormalBasis ℂ ℂ).repr.toLinearEquiv.trans
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (Module.finrank_self ℂ))).toLinearEquiv

theorem tcols_fits (C : Cols B) : Fits (tcols C) (fun _ => 1) where
  mt0 _ := ⟨lineEquiv⟩
  mtTw _ _ := ⟨lineEquiv⟩
  herm u x y := by
    erw [tcols_ipC, tcols_ipC]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]
  pos u x := by
    erw [tcols_ipC]
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun c _ => by rw [Complex.conj_mul']; norm_cast; positivity
  defn u x h := by
    erw [tcols_ipC] at h
    simp only [Complex.conj_mul'] at h
    norm_cast at h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)] at h
    apply Subtype.ext
    funext c t
    have := h c (Finset.mem_univ _)
    have h0 : x.1 c () = 0 := by simpa using this
    exact h0

theorem exists_rows (C₀ : Cols B) (n n₀ a : ℕ) : ∃ (C : Cols B) (W : RowsRest B C),
    W.what₂.Drows = n ∧ W.what₂.D0 = n₀ ∧ (∀ μ j, Module.finrank ℂ (W.what₂.Mt μ j) = a) ∧
      (∀ μ, Module.finrank ℂ (W.what₂.Amb μ) = 1) ∧ (∀ u, Nontrivial (W.what₂.Mu u)) ∧ W.what₂.muStar ≠ W.what₂.mu0 := by
  refine ⟨tcols C₀, model (tcols_fits C₀) n n₀ a, rfl, rfl, fun _ _ => ?_, fun _ => ?_, fun u => ?_, ?_⟩
  · exact finrank_euclideanSpace_fin
  · exact finrank_euclideanSpace_fin
  · classical
    haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    exact Submodule.nontrivial_iff_ne_bot.2
      (GlobalTheory.MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (two_lt_alt B.toPre u))
  · exact Bool.noConfusion

theorem trunc_trunc {a b c : ℕ} (h : a = b) (x : Eu a) : trunc b c (trunc a b x) = trunc a c x := by
  subst h; rw [trunc_self]

theorem mdim_self (n j : ℕ) : mdim n n j = n := by cases j <;> rfl

theorem congr_symm_eq {a b : ℕ} (h : a = b) (x : Eu b) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)).symm x = trunc b a x := by
  subst h; rw [trunc_self]; rfl

theorem model_buDef {C : Cols B} {d : C.Tup → ℕ} (h : Fits C d) (n₀ a : ℕ) :
    Rows.BuDef (model h (d C.mu0) n₀ a).what₂ := by
  have hd : ∀ j (x : Eu (mdim (d C.mu0) (d C.mu0) j)),
      (model h (d C.mu0) n₀ a).what₂.downTo C.mu0 j x = trunc _ (d C.mu0) x := by
    intro j
    induction j with
    | zero => exact fun x => (trunc_self _ x).symm
    | succ j ih =>
      intro x
      exact (ih (trunc _ _ x)).trans (trunc_trunc ((mdim_self _ _).trans (mdim_self _ _).symm) x)
  intro u φ F _
  have hi : (model h (d C.mu0) n₀ a).what₂.iota C.mu0 F = F := by
    refine (hd B.R.m _).trans ?_
    erw [congr_symm_eq (mdim_m B.R (d C.mu0) (d C.mu0)) F]
    exact (trunc_trunc (mdim_self _ _).symm _).trans (trunc_self _ _)
  erw [hi]
  refine ((model h (d C.mu0) n₀ a).perCol_base_eq_PtilCol u φ F).trans ?_
  show _ = (C.mem u).P.PtilCol _ ((h.mt0 u).some.symm (trunc _ _ F))
  erw [trunc_self]
  rfl

theorem model_lamPDef {C : Cols B} {d : C.Tup → ℕ} (h : Fits C d) (n n₀ a : ℕ) :
    Rows.LamPDef (model h n n₀ a).what₂ := by
  intro μ j _ _ σ x _
  show (LinearMap.id : Eu a →ₗ[ℂ] Eu a) (LinearMap.adjoint (LinearMap.id : Eu a →ₗ[ℂ] Eu a) x) = ((1 : ℝ) : ℂ) • (show Eu a from x)
  rw [LinearMap.adjoint_id, Complex.ofReal_one, one_smul]
  rfl

end GlobalTheory.Mem.RowsRestModel

end
