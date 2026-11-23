import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPotential

noncomputable section

namespace GlobalTheory.Mem.RowsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

abbrev Euc (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Euc n) := by
  classical
  exact
    { gen := Finset.univ.image (fun i => EuclideanSpace.basisFun (Fin n) ℂ i)
      span_top := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq }

theorem mem_stdOLat {O : Type} [CommRing O] {φ : O →+* ℂ} {n : ℕ} {x : Euc n}
    (hx : x ∈ (stdOLat O φ n).gen) : ∃ i, EuclideanSpace.basisFun (Fin n) ℂ i = x := by
  classical
  simpa [stdOLat] using hx

def coordEmb {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) : (Fin n → K) →ₛₗ[σ] Euc n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coordEmb_single {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) (i : Fin n) :
    coordEmb σ n (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℂ i := by
  ext j
  by_cases h : j = i
  · subst h; simp [coordEmb]
  · simp [coordEmb, h]

theorem coordEmb_basis {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) {ι : Type}
    (b : Module.Basis ι K (Fin n → K)) :
    LinearIndependent ℂ (fun i => coordEmb σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) = ⊤ := by
  classical
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [OrthonormalBasis.coe_toBasis, ← coordEmb_single σ, ← b.sum_repr (Pi.single i 1), map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs ?_, top_le_iff.mp hs⟩
  rw [← Module.finrank_eq_card_basis b]
  simp

theorem exists_frame {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) :
    ∃ e : Euc (Module.finrank ℂ V) ≃ₗ[ℂ] V, ∀ x y, inner ℂ x y = c.inner (e x) (e y) := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine ⟨(stdOrthonormalBasis ℂ V).repr.symm.toLinearEquiv, fun x y => ?_⟩
  exact ((stdOrthonormalBasis ℂ V).repr.symm.inner_map_map x y).symm

variable {B : Base} (C : Cols B)

def ramCore (u : B.Word)
    (h1 : ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
      (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ))
    (h2 : ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) :
    InnerProductSpace.Core ℂ (C.mem u).A.Mram where
  inner φ ψ := (C.fm u).ipC 0 φ.1 ψ.1
  conj_inner_symm φ ψ := (h1 ψ.1 ψ.2 φ.1 φ.2).symm
  re_inner_nonneg φ := by
    by_cases h : φ.1 = 0
    · show 0 ≤ ((C.fm u).ipC 0 φ.1 φ.1).re
      rw [h]
      simp [MemberForms.ipC]
    · exact (h2 φ.1 φ.2 h).le
  add_left φ ψ χ := by
    show (C.fm u).ipC 0 (φ.1 + ψ.1) χ.1 = _
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left φ ψ r := by
    show (C.fm u).ipC 0 (r • φ.1) ψ.1 = _
    simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm]
  definite φ h := by
    by_contra hne
    have := h2 φ.1 φ.2 (fun h0 => hne (Subtype.ext h0))
    change (C.fm u).ipC 0 φ.1 φ.1 = 0 at h
    rw [h] at this
    simp at this

theorem mram_fd (u : B.Word) : FiniteDimensional ℂ (C.mem u).A.Mram := by
  have := (C.mem u).A.Mu0_fd
  exact Submodule.finiteDimensional_of_le (show (C.mem u).A.Mram ≤ (C.mem u).A.Mu0 from inf_le_left)

def eucCast {a b : ℕ} (h : a = b) : Euc a ≃ₗᵢ[ℂ] Euc b :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)

open Classical in

def model (n : C.Tup → ℕ) (D : ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Euc (n C.mu0)) (eTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Euc (n μ))
    (eM : ∀ u, Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram)
    (heM : ∀ u φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (eM u φ).1 (eM u ψ).1) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.mu0
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Euc D
  Drows := D
  onb := EuclideanSpace.basisFun (Fin D) ℂ
  Dall := D
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Euc D
  D0 := D
  onb0 := EuclideanSpace.basisFun (Fin D) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Euc (n μ)
  Mult μ j := Euc (if j = 0 then D else n μ)
  multZero _ := eucCast (if_pos rfl)
  multTop _ := eucCast (if_neg (by have := B.R.two_le_m; omega))
  io _ _ := Matrix.toEuclideanLin (Matrix.of fun a b => if (a : ℕ) = (b : ℕ) then 1 else 0)
  Mtilde μ := stdOLat _ _ (n μ)
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ _ _ := rfl
  Mu u := Euc (C.mem u).A.du
  perCol u μ φ F :=
    if h : μ = C.mu0 then (C.mem u).P.PtilCol (eM u φ).1 ((e0 u).symm (eucCast (congrArg n h) F))
    else (C.PTw u μ).PtilCol (C.e0Tw u μ (eM u φ).1) ((eTw u μ).symm F)
  Bu _ φ F := (∑ a, φ a) * ∑ b, F b
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Euc D
  MjLat _ := stdOLat _ _ D
  kaBig _ _ _ := 0
  kaSmall _ _ _ := 0
  Mt _ _ := Euc D
  MtLat _ _ := stdOLat _ _ D
  MtL _ _ := Fin D → B.LL
  jMt _ _ := coordEmb B.embLL D
  jMt_basis _ _ b := coordEmb_basis B.embLL D b
  MtLat_sub _ _ x hx := by
    obtain ⟨i, rfl⟩ := mem_stdOLat hx
    exact ⟨_, coordEmb_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ _ _ := rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 0
  shaLen_nonneg _ _ := le_rfl
  eMu := eM
  eMt0 := e0
  perCol_base_eq_PtilCol u φ F := by
    rw [dif_pos rfl]
    rfl
  Bu_linL _ F := ⟨fun φ ψ => by simp [Finset.sum_add_distrib, add_mul],
    fun a φ => by simp [← Finset.mul_sum, mul_assoc]⟩
  Bu_linR _ φ := ⟨fun F G => by simp [Finset.sum_add_distrib, mul_add],
    fun a F => by simp [← Finset.mul_sum, mul_left_comm]⟩
  eMtTw := eTw
  perCol_tie u μ h φ F := dif_neg h
  eMu_isom := heM

end GlobalTheory.Mem.RowsModel

namespace GlobalTheory.Mem

open Formalism.BasicNotions RowsModel in

theorem exists_rowsRest :
    ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (D : ℕ),
      (∀ u, Nonempty ((C.mem u).P.Mt ≃ₗ[ℂ] (Fin (n C.mu0) → ℂ))) →
      (∀ u μ, Nonempty ((C.PTw u μ).Mt ≃ₗ[ℂ] (Fin (n μ) → ℂ))) →
      (∀ u, ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
        (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ)) →
      (∀ u, ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) →
      ∃ W : RowsRest B C, W.Drows = D ∧ W.D0 = D ∧ (∀ μ, Module.finrank ℂ (W.Amb μ) = n μ) ∧
        (∀ μ, W.eOp μ = LinearMap.id) ∧ ∀ μ j, Module.finrank ℂ (W.Mt μ j) = D := by
  intro B C n D h0 hT h1 h2
  have hf : ∀ u, ∃ e : Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := mram_fd C u
    exists_frame (ramCore C u (h1 u) (h2 u))
  choose eM heM using hf
  refine ⟨model C n D (fun u => (h0 u).some.trans (WithLp.linearEquiv 2 ℂ _).symm)
    (fun u μ => (hT u μ).some.trans (WithLp.linearEquiv 2 ℂ _).symm) eM heM, rfl, rfl, fun μ => ?_,
    fun _ => rfl, fun _ _ => ?_⟩
  · exact finrank_euclideanSpace_fin
  · exact finrank_euclideanSpace_fin

theorem RowsModel.ipC_cols (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 φ ψ = ∑ c, starRingEnd ℂ (φ c ()) * ψ c () := by
  refine Finset.sum_congr rfl fun c _ => ?_
  show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ * (starRingEnd ℂ (φ c ()) * ψ c ()) = _
  simp

open Formalism.BasicNotions RowsModel in

theorem exists_cols_rowsRest (B : Base) (D : ℕ) :
    ∃ (C : Cols B) (W : RowsRest B C), W.Drows = D ∧ W.D0 = D ∧ (∀ u, Nontrivial (W.Mu u)) ∧
      (∀ μ, Module.finrank ℂ (W.Amb μ) = 1) ∧ (∀ μ, W.eOp μ = LinearMap.id) ∧
      ∀ μ j, Module.finrank ℂ (W.Mt μ j) = D := by
  classical
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := exists_rowsRest B (ColsModel.cols B) (fun _ => 1) D
    (fun _ => ⟨(LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm⟩)
    (fun _ _ => ⟨(LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm⟩)
    (fun u φ _ ψ _ => by
      rw [ipC_cols, ipC_cols, map_sum]
      exact Finset.sum_congr rfl fun c _ => by simp [mul_comm])
    (fun u φ _ hφ => by
      rw [ipC_cols, Complex.re_sum]
      obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
        by_contra h
        exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
      refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        positivity
      · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        positivity)
  refine ⟨_, W, h1, h2, fun u => ?_, h3, h4, h5⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (W.eMu u).toEquiv.nontrivial

theorem exists_cols_rowsRest_pos (B : Base) :
    ∃ (C : Cols B) (W : RowsRest B C), 0 < W.Drows ∧ ∀ u, Nontrivial (W.Mu u) := by
  obtain ⟨C, W, h, -, h', -⟩ := exists_cols_rowsRest B 1
  exact ⟨C, W, by omega, h'⟩

end GlobalTheory.Mem

end
