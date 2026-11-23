import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSBEventuallySliceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqZeroOfFiberIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

noncomputable section

namespace GlobalTheory.DetEqv.OpenPart

open Set Filter Topology Matrix MeasureTheory GlobalTheory.SplitWeil ValuativeRel

theorem mem_SB_of_subset {X : Type} [TopologicalSpace X] {f : X → ℂ} (hl : IsLocallyConstant f)
    {K : Set X} (hK : IsCompact K) (h : ∀ x, f x ≠ 0 → x ∈ K) : f ∈ SB X := by
  refine ⟨hl, ?_⟩
  have hcl : IsClosed (Function.support f) := (hl.isClopen_fiber 0).compl.isClosed
  refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
  rw [tsupport, hcl.closure_eq]
  exact h

section Ext

variable {W X T : Type} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace T] [T2Space T]

theorem extend_mem_SB {ι : W → X} (hι : IsOpenEmbedding ι) {π : X → T} (hπ : Continuous π) (t₀ : T)
    (hr : ∀ x, x ∈ range ι ↔ π x ≠ t₀) {F : W → ℂ} (hF : F ∈ SB W) :
    Function.extend ι F 0 ∈ SB X := by
  have hK : IsCompact (ι '' tsupport F) := hF.2.isCompact.image hι.continuous
  have hs : ∀ x, Function.extend ι F 0 x ≠ 0 → x ∈ ι '' tsupport F := by
    intro x hx
    by_cases h : ∃ w, ι w = x
    · obtain ⟨w, rfl⟩ := h
      rw [hι.injective.extend_apply] at hx
      exact ⟨w, subset_tsupport _ hx, rfl⟩
    · rw [Function.extend_apply' _ _ _ h] at hx
      exact absurd rfl hx
  refine mem_SB_of_subset ?_ hK hs
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases h : ∃ w, ι w = x
  · obtain ⟨w, rfl⟩ := h
    rw [← hι.map_nhds_eq, eventually_map]
    filter_upwards [hF.1.eventually_eq w] with v hv
    rw [hι.injective.extend_apply, hι.injective.extend_apply, hv]
  · have hx : π x = t₀ := by
      by_contra hne
      exact h ((hr x).2 hne)
    have hc : IsClosed (π '' (ι '' tsupport F)) := (hK.image hπ).isClosed
    have hn : π x ∈ (π '' (ι '' tsupport F))ᶜ := by
      rintro ⟨_, ⟨w, -, rfl⟩, h2⟩
      exact (hr _).1 ⟨w, rfl⟩ (h2.trans hx)
    filter_upwards [hπ.continuousAt.eventually (hc.isOpen_compl.mem_nhds hn)] with y hy
    rw [Function.extend_apply' _ _ _ h]
    by_contra hne
    exact hy ⟨y, hs y hne, rfl⟩

def extZero {ι : W → X} (hι : IsOpenEmbedding ι) {π : X → T} (hπ : Continuous π) (t₀ : T)
    (hr : ∀ x, x ∈ range ι ↔ π x ≠ t₀) : SB W →ₗ[ℂ] SB X where
  toFun F := ⟨Function.extend ι (F : W → ℂ) 0, extend_mem_SB hι hπ t₀ hr F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext x
    by_cases h : ∃ w, ι w = x
    · obtain ⟨w, rfl⟩ := h
      simp [hι.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_smul' c F := by
    apply Subtype.ext
    funext x
    by_cases h : ∃ w, ι w = x
    · obtain ⟨w, rfl⟩ := h
      simp [hι.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

theorem extZero_apply {ι : W → X} (hι : IsOpenEmbedding ι) {π : X → T} (hπ : Continuous π) (t₀ : T)
    (hr : ∀ x, x ∈ range ι ↔ π x ≠ t₀) (F : SB W) (w : W) :
    (extZero hι hπ t₀ hr F : X → ℂ) (ι w) = (F : W → ℂ) w :=
  hι.injective.extend_apply _ _ _

theorem extZero_apply_off {ι : W → X} (hι : IsOpenEmbedding ι) {π : X → T} (hπ : Continuous π) (t₀ : T)
    (hr : ∀ x, x ∈ range ι ↔ π x ≠ t₀) (F : SB W) (x : X) (hx : π x = t₀) :
    (extZero hι hπ t₀ hr F : X → ℂ) x = 0 :=
  Function.extend_apply' _ _ _ fun h => (hr x).1 h hx

theorem exists_extZero {ι : W → X} (hι : IsOpenEmbedding ι) {π : X → T} (hπ : Continuous π) (t₀ : T)
    (hr : ∀ x, x ∈ range ι ↔ π x ≠ t₀) (Φ : SB X) (hΦ : ∀ x, π x = t₀ → (Φ : X → ℂ) x = 0) :
    ∃ F : SB W, extZero hι hπ t₀ hr F = Φ := by
  have hcl : IsClosed (Function.support (Φ : X → ℂ)) := (Φ.2.1.isClopen_fiber 0).compl.isClosed
  have hK : IsCompact (Function.support (Φ : X → ℂ)) := by
    have := Φ.2.2.isCompact
    rwa [tsupport, hcl.closure_eq] at this
  have hK' : IsCompact (ι ⁻¹' Function.support (Φ : X → ℂ)) :=
    hι.isInducing.isCompact_preimage' hK fun x hx => (hr x).2 fun h => hx (hΦ x h)
  refine ⟨⟨(Φ : X → ℂ) ∘ ι, mem_SB_of_subset (Φ.2.1.comp_continuous hι.continuous) hK' fun w hw => hw⟩, ?_⟩
  apply Subtype.ext
  funext x
  by_cases h : π x = t₀
  · rw [extZero_apply_off _ _ _ _ _ _ h, hΦ x h]
  · obtain ⟨w, rfl⟩ := (hr x).2 h
    rw [extZero_apply]
    rfl

end Ext

section Tens

variable {A Z : Type} [TopologicalSpace A] [TopologicalSpace Z]

def tens (χ : SB A) : SB Z →ₗ[ℂ] SB (A × Z) where
  toFun G := ⟨fun p => (χ : A → ℂ) p.1 * (G : Z → ℂ) p.2,
    mem_SB_of_subset ((χ.2.1.comp_continuous continuous_fst).mul (G.2.1.comp_continuous continuous_snd))
      (χ.2.2.isCompact.prod G.2.2.isCompact) fun p hp =>
        ⟨subset_tsupport _ (left_ne_zero_of_mul hp), subset_tsupport _ (right_ne_zero_of_mul hp)⟩⟩
  map_add' F G := by
    apply Subtype.ext
    funext x
    simp [mul_add]
  map_smul' c F := by
    apply Subtype.ext
    funext x
    simp [mul_left_comm]

theorem tens_apply (χ : SB A) (G : SB Z) (u : A) (z : Z) :
    (tens χ G : A × Z → ℂ) (u, z) = (χ : A → ℂ) u * (G : Z → ℂ) z := rfl

end Tens

section Local

theorem nonarchimedean_local_field_t2Space (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem integrable_slice [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    {Z : Type} [TopologicalSpace Z] {p : ℕ} (F : SB ((Fin p → k) × Z)) (z : Z) :
    Integrable (fun u => (F : (Fin p → k) × Z → ℂ) (u, z)) (Measure.pi fun _ : Fin p => ν) := by
  haveI := secondCountable k
  haveI := nonarchimedean_local_field_t2Space k
  have h : (fun u => (F : (Fin p → k) × Z → ℂ) (u, z)) ∈ SB (Fin p → k) :=
    mem_SB_of_subset (F.2.1.comp_continuous (continuous_id.prodMk continuous_const))
      (F.2.2.isCompact.image continuous_fst) fun u hu => ⟨(u, z), subset_tsupport _ hu, rfl⟩
  exact h.1.continuous.integrable_of_hasCompactSupport h.2

theorem exists_SB_integral_one [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (p : ℕ) : ∃ χ : SB (Fin p → k), ∫ u, (χ : (Fin p → k) → ℂ) u ∂(Measure.pi fun _ : Fin p => ν) = 1 := by
  haveI := secondCountable k
  haveI := nonarchimedean_local_field_t2Space k
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  set K : Set (Fin p → k) := Set.pi univ fun _ => (𝒪[k] : Set k) with hKdef
  have hKc : IsCompact K := isCompact_univ_pi fun _ => hc
  have hKo : IsOpen K := isOpen_set_pi finite_univ fun _ _ => ho
  have hcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  set m : Measure (Fin p → k) := Measure.pi fun _ : Fin p => ν
  have h1 : m K ≠ 0 := (hKo.measure_pos m ⟨0, fun _ _ => zero_mem 𝒪[k]⟩).ne'
  have h2 : m K ≠ ⊤ := hKc.measure_lt_top.ne
  have h3 : (m.real K : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h1 h2).ne'
  refine ⟨⟨K.indicator fun _ => (m.real K : ℂ)⁻¹, mem_SB_of_subset
    (LocallyConstant.indicator (LocallyConstant.const _ (m.real K : ℂ)⁻¹) hcl).isLocallyConstant hKc fun x hx => ?_⟩, ?_⟩
  · by_contra hn
    exact hx (indicator_of_notMem hn _)
  · show ∫ u, K.indicator (fun _ => (m.real K : ℂ)⁻¹) u ∂m = 1
    rw [integral_indicator_const _ hKo.measurableSet, Complex.real_smul, mul_inv_cancel₀ h3]

end Local

section Descent

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comp_vecMul_mem_SB {m : ℕ} (χ : SB (Fin m → k)) (g : GL (Fin m) k) :
    (fun u => (χ : (Fin m → k) → ℂ) (u ᵥ* (g : Matrix (Fin m) (Fin m) k))) ∈ SB (Fin m → k) := by
  refine mem_SB_of_subset (χ.2.1.comp_continuous (continuous_id.matrix_vecMul continuous_const))
    (χ.2.2.isCompact.image (f := fun v => v ᵥ* ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
      (continuous_id.matrix_vecMul continuous_const)) fun u hu => ⟨_, subset_tsupport _ hu, ?_⟩
  show (u ᵥ* _) ᵥ* _ = u
  rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]

theorem integral_comp_vecMul [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    {m : ℕ} (g : GL (Fin m) k) (f : (Fin m → k) → ℂ) :
    ∫ u, f (u ᵥ* (g : Matrix (Fin m) (Fin m) k)) ∂(Measure.pi fun _ => ν) =
      ((nabs k (GeneralLinearGroup.det g) : ℂ))⁻¹ * ∫ u, f u ∂(Measure.pi fun _ => ν) := by
  have hd : (g : Matrix (Fin m) (Fin m) k)ᵀ.det ≠ 0 := by
    rw [det_transpose]
    exact (GeneralLinearGroup.det g).ne_zero
  have h := integral_comp_mulVec_eq_smul ν (GeneralLinearGroup.mkOfDetNeZero _ hd) f
  have e : GeneralLinearGroup.det (GeneralLinearGroup.mkOfDetNeZero _ hd) = GeneralLinearGroup.det g := by
    ext
    exact det_transpose _
  rw [e, Complex.real_smul, Complex.ofReal_inv] at h
  rw [← h]
  congr 1
  funext u
  congr 1
  exact (mulVec_transpose _ _).symm

theorem descent {n : ℕ} (hV : VanishAt k n) {Y : Type} [TopologicalSpace Y] {m : ℕ} (hnm : n < m)
    (μ : kˣ →* ℂˣ) (hμ : ∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ))
    (L : SB ((Fin m → k) × (Y × Matrix (Fin n) (Fin m) k)) →ₗ[ℂ] ℂ)
    (hL : ∀ (c : Fin m → k) (g : GL (Fin m) k) (F F' : SB ((Fin m → k) × (Y × Matrix (Fin n) (Fin m) k))),
      (∀ u y R, (F' : (Fin m → k) × (Y × Matrix (Fin n) (Fin m) k) → ℂ) (u, y, R) =
        (F : (Fin m → k) × (Y × Matrix (Fin n) (Fin m) k) → ℂ)
          (c + u ᵥ* (g : Matrix (Fin m) (Fin m) k), y, R * (g : Matrix (Fin m) (Fin m) k))) →
      L F' = (μ (GeneralLinearGroup.det g) : ℂ) * L F) : L = 0 := by
  borelize k
  haveI := nonarchimedean_local_field_t2Space k
  let ν : Measure k := Measure.addHaar
  obtain ⟨χ, hχ⟩ := exists_SB_integral_one ν m
  have key : ∀ (F : SB ((Fin m → k) × (Y × Matrix (Fin n) (Fin m) k)))
      (G : SB (Y × Matrix (Fin n) (Fin m) k)),
      (∀ z, ∫ u, (F : (Fin m → k) × (Y × Matrix (Fin n) (Fin m) k) → ℂ) (u, z)
        ∂(Measure.pi fun _ : Fin m => ν) = (G : Y × Matrix (Fin n) (Fin m) k → ℂ) z) →
      L F = L (tens χ G) := by
    intro F G h
    rw [← sub_eq_zero, ← map_sub]
    refine GlobalTheory.DetEqv.Transl.map_eq_zero_of_fiber_integral k ν _ m L ?_ _ fun z => ?_
    · intro c Φ Φ' hΦ
      have := hL c 1 Φ Φ' fun u y R => by
        rw [hΦ, Units.val_one, vecMul_one, Matrix.mul_one, add_comm]
      simpa using this
    · have := integral_sub (integrable_slice ν F z) (integrable_slice ν (tens χ G) z)
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [this, h]
      simp only [tens_apply]
      rw [integral_mul_const, hχ, one_mul, sub_self]
  have h0 : L ∘ₗ tens χ = 0 := by
    refine hV Y m hnm (μ * GlobalTheory.SmGL.absPow k 1) (fun t ht => hμ (t - 1) ?_) _ fun g G G' hG => ?_
    · rw [Complex.ofReal_sub, sub_eq_add_neg, GlobalTheory.SmGL.absPow_add, ← ht, Complex.ofReal_one,
        GlobalTheory.SmGL.absPow_neg, mul_inv_cancel_right]
    · have hN : (nabs k (GeneralLinearGroup.det g) : ℂ) ≠ 0 := by
        exact_mod_cast (GlobalTheory.SmGL.nabs_pos' k _).ne'
      have e1 := hL 0 g (tens χ G) (tens ⟨_, comp_vecMul_mem_SB χ g⟩ G') fun u y R => by
        rw [tens_apply, tens_apply, zero_add, hG]
      have e2 := key (tens ⟨_, comp_vecMul_mem_SB χ g⟩ G')
        (((nabs k (GeneralLinearGroup.det g) : ℂ))⁻¹ • G') fun z => by
          simp only [tens_apply]
          rw [integral_mul_const, integral_comp_vecMul, hχ, mul_one]
          rfl
      rw [e2, map_smul, map_smul, smul_eq_mul] at e1
      simp only [LinearMap.comp_apply, MonoidHom.mul_apply, Units.val_mul, GlobalTheory.SmGL.val_absPow,
        Complex.cpow_one]
      rw [mul_right_comm, ← e1]
      field_simp
  ext F
  rw [key F ⟨_, fibre_integral_mem_SB k ν _ m F F.2⟩ fun z => rfl]
  exact LinearMap.congr_fun h0 _

end Descent

section Chart

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n m : ℕ} {Y : Type} [TopologicalSpace Y]

def chartMat {K : Type} [CommRing K] (u : Fin m → K) (s : K) (a : Fin n → K) (R : Matrix (Fin n) (Fin m) K) :
    Matrix (Fin (n + 1)) (Fin (m + 1)) K :=
  Matrix.of (vecCons (vecCons s fun j => s * u j) fun l => vecCons (a l) fun j => R l j + a l * u j)

def blockMat {K : Type} [CommRing K] (c : Fin m → K) (g : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of (vecCons (vecCons 1 c) fun i => vecCons 0 (g i))

theorem det_blockMat {K : Type} [CommRing K] (c : Fin m → K) (g : Matrix (Fin m) (Fin m) K) :
    (blockMat c g).det = g.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp [blockMat]
  rfl

theorem mul_blockMat_zero {K : Type} [CommRing K] (X : Matrix (Fin (n + 1)) (Fin (m + 1)) K)
    (c : Fin m → K) (g : Matrix (Fin m) (Fin m) K) : (X * blockMat c g) 0 0 = X 0 0 := by
  simp [blockMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chartMat_mul_blockMat {K : Type} [CommRing K] (u : Fin m → K) (s : K) (a : Fin n → K)
    (R : Matrix (Fin n) (Fin m) K) (c : Fin m → K) (g : Matrix (Fin m) (Fin m) K) :
    chartMat u s a R * blockMat c g = chartMat (c + u ᵥ* g) s a (R * g) := by
  ext i j
  refine Fin.cases ?_ (fun l => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [chartMat, blockMat, Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct, mul_add, add_mul,
      Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
  ring

def chart (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (Y : Type) [TopologicalSpace Y] :
    ((Fin m → k) × ((Y × {s : k // s ≠ 0} × (Fin n → k)) × Matrix (Fin n) (Fin m) k)) ≃ₜ
      {x : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k | x.2 0 0 ≠ 0} where
  toFun w := ⟨(w.2.1.1, chartMat w.1 w.2.1.2.1.1 w.2.1.2.2 w.2.2), w.2.1.2.1.2⟩
  invFun x := (fun j => x.1.2 0 j.succ / x.1.2 0 0, (x.1.1, ⟨x.1.2 0 0, x.2⟩, fun l => x.1.2 l.succ 0),
    Matrix.of fun l j => x.1.2 l.succ j.succ - x.1.2 l.succ 0 * (x.1.2 0 j.succ / x.1.2 0 0))
  left_inv := by
    rintro ⟨u, ⟨y, ⟨s, hs⟩, a⟩, R⟩
    have h : ∀ j, s * u j / s = u j := fun j => mul_div_cancel_left₀ _ hs
    refine Prod.ext (funext fun j => h j) (Prod.ext rfl ?_)
    ext l j
    simp [chartMat, h]
  right_inv := by
    rintro ⟨⟨y, X⟩, hX⟩
    have hX' : X 0 0 ≠ 0 := hX
    refine Subtype.ext (Prod.ext rfl ?_)
    ext i j
    refine Fin.cases ?_ (fun l => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [chartMat, mul_div_cancel₀ _ hX']
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun l => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp only [chartMat, of_apply, cons_val_zero, cons_val_succ] <;> fun_prop
  continuous_invFun := by
    have h : ∀ i j, Continuous fun x : {x : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k | x.2 0 0 ≠ 0} =>
        x.1.2 i j := fun i j => by fun_prop
    have hd : ∀ j : Fin m, Continuous fun x : {x : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k | x.2 0 0 ≠ 0} =>
        x.1.2 0 j.succ / x.1.2 0 0 := fun j => (h _ _).div (h _ _) fun x => x.2
    refine (continuous_pi hd).prodMk (Continuous.prodMk (Continuous.prodMk (by fun_prop)
      (Continuous.prodMk ((h 0 0).subtype_mk _) (continuous_pi fun l => h _ _))) ?_)
    exact continuous_matrix fun l j => (h _ _).sub ((h _ _).mul (hd j))

end Chart

theorem vanish_of_vanish_on_corner_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), GlobalTheory.DetEqv.VanishAt k n → ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ), n < m →
    ∀ μ : kˣ →* ℂˣ, (∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) → ∀ L : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k) →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (m + 1)) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k)),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k),
          (Φ' : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) =
            (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      ∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k), X 0 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) = 0) →
        L Φ = 0 := by
  intro k _ _ _ _ n hV Y _ m hnm μ hμ L hL Φ hΦ
  haveI := nonarchimedean_local_field_t2Space k
  have hπ : Continuous fun x : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k => x.2 0 0 := by fun_prop
  have hU : IsOpen {x : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k | x.2 0 0 ≠ 0} :=
    isOpen_ne_fun hπ continuous_const
  have hι : IsOpenEmbedding (Subtype.val ∘ chart k n m Y) :=
    hU.isOpenEmbedding_subtypeVal.comp (chart k n m Y).isOpenEmbedding
  have hr : ∀ x, x ∈ range (Subtype.val ∘ chart k n m Y) ↔ x.2 0 0 ≠ 0 := by
    intro x
    rw [(chart k n m Y).surjective.range_comp, Subtype.range_coe]
    rfl
  have h0 : L ∘ₗ extZero hι hπ 0 hr = 0 := by
    refine descent hV hnm μ hμ _ fun c g F F' hF => ?_
    have hd : (blockMat c (g : Matrix (Fin m) (Fin m) k)).det ≠ 0 := by
      rw [det_blockMat]
      exact (GeneralLinearGroup.det g).ne_zero
    have e : GeneralLinearGroup.det (GeneralLinearGroup.mkOfDetNeZero _ hd) = GeneralLinearGroup.det g := by
      ext
      exact det_blockMat _ _
    rw [← e]
    refine hL _ _ _ fun y X => ?_
    show _ = (extZero hι hπ 0 hr F : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X * blockMat c g)
    by_cases hX : X 0 0 = 0
    · rw [extZero_apply_off _ _ _ _ _ (y, X) hX,
        extZero_apply_off _ _ _ _ _ (y, X * blockMat c g) ((mul_blockMat_zero X _ _).trans hX)]
    · obtain ⟨⟨u, ⟨y', s, a⟩, R⟩, hw⟩ := (hr (y, X)).2 hX
      have h1 : y' = y := congrArg Prod.fst hw
      have h2 : chartMat u s.1 a R = X := congrArg Prod.snd hw
      have h3 : (y, X * blockMat c (g : Matrix (Fin m) (Fin m) k)) = (Subtype.val ∘ chart k n m Y)
          (c + u ᵥ* (g : Matrix (Fin m) (Fin m) k), (y', s, a), R * (g : Matrix (Fin m) (Fin m) k)) := by
        rw [← h1, ← h2, chartMat_mul_blockMat]
        rfl
      rw [h3, ← hw, extZero_apply, extZero_apply, hF]
  obtain ⟨F, rfl⟩ := exists_extZero hι hπ 0 hr Φ fun x hx => hΦ x.1 x.2 hx
  exact LinearMap.congr_fun h0 F

end GlobalTheory.DetEqv.OpenPart
