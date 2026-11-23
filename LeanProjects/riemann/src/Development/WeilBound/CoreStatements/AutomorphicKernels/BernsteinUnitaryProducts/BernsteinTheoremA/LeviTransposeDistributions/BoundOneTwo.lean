import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.TheoremAFromLeviTranspose.TheoremAOfLeviTranspose

noncomputable section

open Matrix Topology Filter ValuativeRel GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.GelfandKazhdan PositivityTheory.PfBern.ThmA

namespace PositivityTheory.PfBern.cocyclesToWachVectorsExponent

section Levi

variable {k : Type} [Field k]

theorem trGL_glEmb (n : ℕ) (g : GL (Fin n) k) : trGL (glEmb k n g) = glEmb k n (trGL g) := by
  apply Units.ext
  show ((glEmb k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ =
    glEmbMat k n ((g : Matrix (Fin n) (Fin n) k)ᵀ)
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [glEmb, glEmbHom, glEmbMat]

theorem trGL_inv' {m : ℕ} (g : GL (Fin m) k) : trGL g⁻¹ = (trGL g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trGL_mul, mul_inv_cancel]
  exact Units.ext (by show ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ = 1; simp)

end Levi

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {m : ℕ}

theorem isEmbedding_valGL : IsEmbedding (Units.val : GL (Fin m) k → Matrix (Fin m) (Fin m) k) := by
  refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
  · intro A hA
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_matrix_inv
    have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  · intro u
    exact (Matrix.coe_units_inv u).symm

theorem range_valGL :
    Set.range (Units.val : GL (Fin m) k → Matrix (Fin m) (Fin m) k) = {A | A.det ≠ 0} := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
  · intro h
    exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)).unit, IsUnit.unit_spec _⟩

variable [T2Space k]

theorem isOpenEmbedding_valGL :
    IsOpenEmbedding (Units.val : GL (Fin m) k → Matrix (Fin m) (Fin m) k) where
  toIsEmbedding := isEmbedding_valGL
  isOpen_range := by
    rw [range_valGL]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const

open scoped Classical in

def extZ (φ : SB (GL (Fin m) k)) : Matrix (Fin m) (Fin m) k → ℂ :=
  fun y => if h : IsUnit y then φ.1 h.unit else 0

theorem extZ_val (φ : SB (GL (Fin m) k)) (u : GL (Fin m) k) : extZ φ u.val = φ.1 u := by
  rw [extZ, dif_pos u.isUnit, IsUnit.unit_of_val_units]

theorem extZ_mem (φ : SB (GL (Fin m) k)) : extZ φ ∈ SB (Matrix (Fin m) (Fin m) k) := by
  have hE := isOpenEmbedding_valGL (k := k) (m := m)
  have hK : IsCompact (Units.val '' tsupport φ.1) := φ.2.2.isCompact.image hE.continuous
  have hKc : IsClosed (Units.val '' tsupport φ.1) := hK.isClosed
  have hzero : ∀ y, y ∉ Units.val '' tsupport φ.1 → extZ φ y = 0 := by
    intro y hy
    unfold extZ
    split_ifs with h
    · exact image_eq_zero_of_notMem_tsupport (fun hm => hy ⟨h.unit, hm, h.unit_spec⟩)
    · rfl
  refine ⟨?_, HasCompactSupport.intro' hK hKc hzero⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    have hφ := (IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 u
    rw [← hE.map_nhds_eq, Filter.eventually_map]
    filter_upwards [hφ] with u' hu'
    rw [extZ_val, extZ_val, hu']
  · have hy' : y ∉ Units.val '' tsupport φ.1 := by
      rintro ⟨u, -, rfl⟩
      exact hy u.isUnit
    filter_upwards [hKc.isOpen_compl.mem_nhds hy'] with y' hy''
    rw [hzero y' hy'', hzero y hy']

open scoped Classical in

def cutFun (U : Set k) (ψ : SB (Matrix (Fin m) (Fin m) k)) : GL (Fin m) k → ℂ :=
  fun x => if (x.val).det ∈ U then ψ.1 x.val else 0

theorem cutFun_mem (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) (ψ : SB (Matrix (Fin m) (Fin m) k)) :
    cutFun U ψ ∈ SB (GL (Fin m) k) := by
  have hdet : Continuous fun x : GL (Fin m) k => (x.val).det := Units.continuous_val.matrix_det
  constructor
  · have h1 : IsLocallyConstant (fun x : GL (Fin m) k => ψ.1 x.val) :=
      ψ.2.1.comp_continuous Units.continuous_val
    rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
    intro x
    by_cases hx : (x.val).det ∈ U
    · have h2 : ∀ᶠ x' in 𝓝 x, (x'.val).det ∈ U :=
        hdet.continuousAt.preimage_mem_nhds (hU.isOpen.mem_nhds hx)
      filter_upwards [h2, h1 x] with x' hx' h'
      simp only [cutFun, if_pos hx, if_pos hx', h']
    · have h2 : ∀ᶠ x' in 𝓝 x, (x'.val).det ∈ Uᶜ :=
        hdet.continuousAt.preimage_mem_nhds (hU.isClosed.isOpen_compl.mem_nhds hx)
      filter_upwards [h2] with x' hx'
      have hx'' : (x'.val).det ∉ U := hx'
      simp only [cutFun, if_neg hx, if_neg hx'']
  · have hK : IsCompact (tsupport ψ.1 ∩ (fun A : Matrix (Fin m) (Fin m) k => A.det) ⁻¹' U) :=
      ψ.2.2.isCompact.inter_right (hU.isClosed.preimage continuous_id.matrix_det)
    have hKr : tsupport ψ.1 ∩ (fun A : Matrix (Fin m) (Fin m) k => A.det) ⁻¹' U ⊆
        Set.range (Units.val : GL (Fin m) k → Matrix (Fin m) (Fin m) k) := by
      intro A hA
      rw [range_valGL]
      show A.det ≠ 0
      intro h
      have hA2 : A.det ∈ U := hA.2
      rw [h] at hA2
      exact h0 hA2
    have hK' := isEmbedding_valGL.isInducing.isCompact_preimage' hK hKr
    refine HasCompactSupport.intro' hK' (hK.isClosed.preimage Units.continuous_val) ?_
    intro x hx
    simp only [cutFun]
    split_ifs with h
    · exact image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨hm, h⟩)
    · rfl

def cut (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) :
    SB (Matrix (Fin m) (Fin m) k) →ₗ[ℂ] SB (GL (Fin m) k) where
  toFun ψ := ⟨cutFun U ψ, cutFun_mem U hU h0 ψ⟩
  map_add' ψ₁ ψ₂ := Subtype.ext (funext fun x => by
    simp only [cutFun, Submodule.coe_add, Pi.add_apply]
    split_ifs <;> simp)
  map_smul' c ψ := Subtype.ext (funext fun x => by
    simp only [cutFun, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp)

theorem cut_apply (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) (ψ : SB (Matrix (Fin m) (Fin m) k))
    (x : GL (Fin m) k) : (cut U hU h0 ψ).1 x = cutFun U ψ x := rfl

end Top

section Dist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem t2Space_local : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x},
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem ((valuation k).ne_zero_iff.2 hx), ?_⟩
  exact fun h => lt_irrefl (valuation k x) h

theorem exists_clopen_local (C : Set k) (hC : IsCompact C) (h0 : (0 : k) ∉ C) :
    ∃ U : Set k, IsClopen U ∧ C ⊆ U ∧ (0 : k) ∉ U := by
  have := t2Space_local (k := k)
  have hCc : Cᶜ ∈ 𝓝 (0 : k) := hC.isClosed.isOpen_compl.mem_nhds h0
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hCc
  let W : AddSubgroup k :=
    { carrier := {x | valuation k x < γ}
      add_mem' := fun {a b} ha hb =>
        show valuation k (a + b) < γ from lt_of_le_of_lt ((valuation k).map_add a b) (max_lt ha hb)
      zero_mem' := by
        show valuation k 0 < γ
        rw [map_zero]
        exact zero_lt_iff.2 hγ
      neg_mem' := fun {a} ha => by
        show valuation k (-a) < γ
        rw [Valuation.map_neg]
        exact ha }
  have hWn : (W : Set k) ∈ 𝓝 (0 : k) := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ
  have hWo : IsOpen (W : Set k) := AddSubgroup.isOpen_of_mem_nhds W hWn
  refine ⟨(W : Set k)ᶜ, ⟨hWo.isClosed_compl, (AddSubgroup.isClosed_of_isOpen W hWo).isOpen_compl⟩, ?_, ?_⟩
  · intro c hc hcW
    exact hsub hcW hc
  · exact fun h => h W.zero_mem

def TrAnti {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ψ : SB (GL (Fin m) k), (∀ x y : GL (Fin m) k, y.val = x.val.transpose → ψ.1 x = φ.1 y) → T ψ = -T φ

def NoSignDistGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ T : SB (GL (Fin (n + 1)) k) →ₗ[ℂ] ℂ,
    (∀ g : GL (Fin n) k, ConjInv T (glEmb k n g)) → TrAnti T → T = 0

theorem trInv_iff {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) :
    TrInv T ↔ ∀ φ, T (pull trHomeo φ) = T φ := by
  constructor
  · intro h φ
    exact h φ _ fun x y hy => by
      have : y = trGL x := Units.ext hy
      rw [this]
      rfl
  · intro h φ ψ hψ
    have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => hψ x (trGL x) rfl)
    rw [e]
    exact h φ

theorem trAnti_iff {m : ℕ} (T : SB (GL (Fin m) k) →ₗ[ℂ] ℂ) :
    TrAnti T ↔ ∀ φ, T (pull trHomeo φ) = -T φ := by
  constructor
  · intro h φ
    exact h φ _ fun x y hy => by
      have : y = trGL x := Units.ext hy
      rw [this]
      rfl
  · intro h φ ψ hψ
    have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => hψ x (trGL x) rfl)
    rw [e]
    exact h φ

theorem pull_tr_tr {m : ℕ} (φ : SB (GL (Fin m) k)) : pull trHomeo (pull trHomeo φ) = φ :=
  Subtype.ext (funext fun _ => rfl)

theorem pull_tr_conj {m : ℕ} (g : GL (Fin m) k) (φ : SB (GL (Fin m) k)) :
    pull trHomeo (pull (conjHomeo g) φ) = pull (conjHomeo (trGL g)⁻¹) (pull trHomeo φ) := by
  refine Subtype.ext (funext fun x => ?_)
  show φ.1 (g * trGL x * g⁻¹) = φ.1 (trGL ((trGL g)⁻¹ * x * (trGL g)⁻¹⁻¹))
  congr 1
  simp only [inv_inv, trGL_mul, trGL_inv', trGL_trGL, mul_assoc]

theorem leviTransposeInv_of_noSignDistGL (h : NoSignDistGL k) : LeviTransposeInv k := by
  intro n hn T hT
  have hL : ∀ g : GL (Fin n) k, ConjInv (T - T ∘ₗ pull trHomeo) (glEmb k n g) := by
    intro g
    rw [conjInv_iff]
    intro φ
    have h1 := (conjInv_iff T _).1 (hT g) φ
    have h2 := (conjInv_iff T _).1 (hT (trGL g)⁻¹) (pull trHomeo φ)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [pull_tr_conj, trGL_glEmb, ← map_inv, h2, h1]
  have hA : TrAnti (T - T ∘ₗ pull trHomeo) := by
    rw [trAnti_iff]
    intro φ
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, pull_tr_tr]
    ring
  have h0 := h n hn _ hL hA
  rw [trInv_iff]
  intro φ
  have := congrArg (fun L : SB (GL (Fin (n + 1)) k) →ₗ[ℂ] ℂ => L φ) h0
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply] at this
  exact (sub_eq_zero.1 this).symm

theorem noSignDistGL_of_leviTransposeInv (h : LeviTransposeInv k) : NoSignDistGL k := by
  intro n hn T hL hA
  have hT := (trInv_iff T).1 (h n hn T hL)
  have hA' := (trAnti_iff T).1 hA
  refine LinearMap.ext fun φ => ?_
  have e : T φ = -T φ := by rw [← hA' φ, hT φ]
  rw [LinearMap.zero_apply]
  linear_combination e / 2

theorem noSignDistGL_iff : NoSignDistGL k ↔ LeviTransposeInv k :=
  ⟨leviTransposeInv_of_noSignDistGL, noSignDistGL_of_leviTransposeInv⟩

def ConjInvM {m : ℕ} (T : SB (Matrix (Fin m) (Fin m) k) →ₗ[ℂ] ℂ) (g : GL (Fin m) k) : Prop :=
  ∀ φ ψ : SB (Matrix (Fin m) (Fin m) k),
    (∀ x, ψ.1 x = φ.1 ((g : Matrix (Fin m) (Fin m) k) * x * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))) →
      T ψ = T φ

def TrAntiM {m : ℕ} (T : SB (Matrix (Fin m) (Fin m) k) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ψ : SB (Matrix (Fin m) (Fin m) k), (∀ x, ψ.1 x = φ.1 x.transpose) → T ψ = -T φ

def NoSignDistGl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ T : SB (Matrix (Fin (n + 1)) (Fin (n + 1)) k) →ₗ[ℂ] ℂ,
    (∀ g : GL (Fin n) k, ConjInvM T (glEmb k n g)) → TrAntiM T → T = 0

theorem det_conj_val {m : ℕ} (h x : GL (Fin m) k) :
    ((h : Matrix (Fin m) (Fin m) k) * (x : Matrix (Fin m) (Fin m) k) *
      ((h⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)).det = (x : Matrix (Fin m) (Fin m) k).det := by
  rw [Matrix.coe_units_inv, Matrix.det_conj h.isUnit]

theorem det_conj_gl {m : ℕ} (h x : GL (Fin m) k) :
    (((h * x * h⁻¹ : GL (Fin m) k)) : Matrix (Fin m) (Fin m) k).det = (x : Matrix (Fin m) (Fin m) k).det := by
  rw [Units.val_mul, Units.val_mul, det_conj_val]

theorem noSignDistGL_of_gl (h : NoSignDistGl k) : NoSignDistGL k := by
  have := t2Space_local (k := k)
  intro n hn T hL hA
  refine LinearMap.ext fun φ => ?_
  obtain ⟨U, hU, hCU, h0⟩ := exists_clopen_local
    ((fun x : GL (Fin (n + 1)) k => (x.val).det) '' tsupport φ.1)
    (φ.2.2.isCompact.image Units.continuous_val.matrix_det)
    (by
      rintro ⟨x, -, hx⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hx)
  have hζL : ∀ g : GL (Fin n) k, ConjInvM (T ∘ₗ cut U hU h0) (glEmb k n g) := by
    intro g φ' ψ' hψ'
    simp only [LinearMap.comp_apply]
    apply hL g (cut U hU h0 φ') (cut U hU h0 ψ')
    intro x
    rw [cut_apply, cut_apply]
    have hd := det_conj_gl (glEmb k n g) x
    unfold cutFun
    by_cases hx : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det ∈ U
    · rw [if_pos hx, if_pos (hd ▸ hx), hψ', Units.val_mul, Units.val_mul]
    · rw [if_neg hx, if_neg (hd ▸ hx)]
  have hζA : TrAntiM (T ∘ₗ cut U hU h0) := by
    intro φ' ψ' hψ'
    simp only [LinearMap.comp_apply]
    apply hA (cut U hU h0 φ') (cut U hU h0 ψ')
    intro x y hy
    rw [cut_apply, cut_apply]
    simp only [cutFun]
    rw [hψ', hy, Matrix.det_transpose]
  have hz := h n hn _ hζL hζA
  have hφ : cut U hU h0 ⟨extZ φ, extZ_mem φ⟩ = φ := by
    refine Subtype.ext (funext fun x => ?_)
    rw [cut_apply]
    simp only [cutFun, extZ_val]
    split_ifs with hx
    · rfl
    · exact (image_eq_zero_of_notMem_tsupport (fun hm => hx (hCU ⟨x, hm, rfl⟩))).symm
  rw [LinearMap.zero_apply, ← hφ]
  exact congrArg (fun L : SB (Matrix (Fin (n + 1)) (Fin (n + 1)) k) →ₗ[ℂ] ℂ => L ⟨extZ φ, extZ_mem φ⟩) hz

theorem leviTransposeInv_of_gl (h : NoSignDistGl k) : LeviTransposeInv k :=
  leviTransposeInv_of_noSignDistGL (noSignDistGL_of_gl h)

theorem theoremA_of_gl (h : NoSignDistGl k) : TheoremA k :=
  theoremA_of_levi_transpose (leviTransposeInv_of_gl h)

end Dist

end PositivityTheory.PfBern.cocyclesToWachVectorsExponent

end
