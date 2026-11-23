import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

section ExWAConstruction

variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]

def exwaShift : (ZMod n → LL) ≃ₗ[LL] (ZMod n → LL) :=
  LinearEquiv.funCongrLeft LL LL (Equiv.subRight (1 : ZMod n))

lemma exwaShift_apply (x : ZMod n → LL) (i : ZMod n) : exwaShift x i = x (i - 1) := rfl

lemma exwaShift_single (j : ZMod n) :
    exwaShift (Pi.single j (1 : LL) : ZMod n → LL) = Pi.single (j + 1) 1 := by
  funext i
  simp only [exwaShift_apply, Pi.single_apply, sub_eq_iff_eq_add]

def exwaPhi (c : LL) (hc : c ≠ 0) : (ZMod n → LL) ≃ₗ[LL] (ZMod n → LL) :=
  exwaShift.trans (LinearEquiv.smulOfNeZero LL (ZMod n → LL) c hc)

lemma exwaPhi_apply (c : LL) (hc : c ≠ 0) (x : ZMod n → LL) :
    exwaPhi c hc x = c • exwaShift x := rfl

lemma exwaPhi_single (c : LL) (hc : c ≠ 0) (j : ZMod n) :
    exwaPhi c hc (Pi.single j (1 : LL) : ZMod n → LL) = c • Pi.single (j + 1) 1 := by
  rw [exwaPhi_apply, exwaShift_single]

lemma exwa_internal :
    DirectSum.IsInternal (fun i : ZMod n => LL ∙ (Pi.single i (1 : LL) : ZMod n → LL)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · have h := (Pi.basisFun LL (ZMod n)).linearIndependent.iSupIndep_span_singleton
    simpa using h
  · have h := (Pi.basisFun LL (ZMod n)).span_eq
    rw [Submodule.span_range_eq_iSup] at h
    simpa using h

def exwaF (c : LL) (hc : c ≠ 0) : FilPhi LL (ZMod n → LL) n (ZMod n) where
  letter := id
  e := 1
  fiber := by intro i; simp [Finset.filter_eq']
  Dl := fun i => LL ∙ (Pi.single i (1 : LL) : ZMod n → LL)
  internal := exwa_internal
  φ := exwaPhi c hc
  φ_Dl := by
    intro i
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, exwaPhi_single,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  Fil := fun τ a => if a ≤ -1 then LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL) else ⊥
  Fil_le := by intro τ a; split_ifs <;> simp
  Fil_anti := by
    intro τ a
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | (exfalso; omega)
  lo := -1
  hi := 0
  lo_le := by norm_num
  Fil_lo := by intro τ a ha; exact if_pos ha
  Fil_hi := by intro τ a ha; exact if_neg (by omega)

lemma exwaF_Dl (c : LL) (hc : c ≠ 0) (i : ZMod n) :
    (exwaF c hc).Dl i = LL ∙ (Pi.single i (1 : LL) : ZMod n → LL) := rfl

lemma exwaF_φ (c : LL) (hc : c ≠ 0) (x : ZMod n → LL) : (exwaF c hc).φ x = exwaPhi c hc x := rfl

lemma exwaFiltration_neg_one_eq_span_single (c : LL) (hc : c ≠ 0) (τ : ZMod n) :
    (exwaF c hc).Fil τ (-1) = LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL) := by
  simp [exwaF]

lemma exwaF_Fil_0 (c : LL) (hc : c ≠ 0) (τ : ZMod n) : (exwaF c hc).Fil τ 0 = ⊥ := by
  simp [exwaF]

lemma exwaF_tH (c : LL) (hc : c ≠ 0) (D' : Submodule LL (ZMod n → LL)) :
    (exwaF c hc).tH D' =
      -∑ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ D') : ℤ) := by
  have hI : Finset.Ico (-1 : ℤ) 0 = {-1} := by ext a; simp; omega
  simp only [FilPhi.tH, FilPhi.tHw, FilPhi.mult]
  show ∑ τ, ∑ a ∈ Finset.Ico (-1 : ℤ) 0, a * _ = _
  rw [hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_singleton, show (-1 : ℤ) + 1 = 0 by norm_num, exwaFiltration_neg_one_eq_span_single, exwaF_Fil_0, bot_inf_eq,
    finrank_bot]
  push_cast
  ring

lemma exwaF_tH_top (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).tH ⊤ = -(n : ℤ) := by
  rw [exwaF_tH]
  have h1 : ∀ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ ⊤) : ℤ) = 1 := by
    intro τ
    rw [inf_top_eq, finrank_span_singleton (by simp)]
    rfl
  simp only [h1, Finset.sum_const, Finset.card_univ, ZMod.card n, nsmul_eq_mul, mul_one]

lemma exwaF_tH_bot (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).tH ⊥ = 0 := by
  rw [exwaF_tH]
  have h1 : ∀ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ ⊥) : ℤ) = 0 := by
    intro τ
    rw [inf_bot_eq, finrank_bot]
    rfl
  simp only [h1, Finset.sum_const_zero, neg_zero]

lemma exwaPhi_pow_apply (c : LL) (hc : c ≠ 0) (k : ℕ) (x : ZMod n → LL) :
    (((exwaPhi (n := n) c hc).toLinearMap ^ k) x) =
      c ^ k • fun i => x (i - k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, exwaPhi_apply, exwaShift_apply,
      Nat.cast_succ, sub_sub, pow_succ]
    ring

lemma exwaPhi_pow_n (c : LL) (hc : c ≠ 0) :
    (exwaPhi (n := n) c hc).toLinearMap ^ n = c ^ n • 1 := by
  refine LinearMap.ext fun x => ?_
  rw [exwaPhi_pow_apply, ZMod.natCast_self]
  simp

end ExWAConstruction

section ExWAVal

variable {LL : Type} [Field LL]

lemma exwa_nsmul_top (k : ℕ) (hk : k ≠ 0) : k • (⊤ : WithTop ℚ) = ⊤ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [succ_nsmul, WithTop.add_top]

lemma exwa_val_det {M : Type} [AddCommGroup M] [Module LL M] [FiniteDimensional LL M]
    (v : AddValuation LL (WithTop ℚ)) (f : M →ₗ[LL] M) (k : ℕ) (hk : k ≠ 0)
    (hdim : finrank LL M = k) (c : LL) (r : ℚ) (hf : f ^ k = c • 1) (hc : v c = (r : WithTop ℚ)) :
    v (LinearMap.det f) = (r : WithTop ℚ) := by
  have h1 : (LinearMap.det f) ^ k = c ^ k := by
    rw [← map_pow, hf, LinearMap.det_smul, map_one, mul_one, hdim]
  have h2 : k • v (LinearMap.det f) = ((k • r : ℚ) : WithTop ℚ) := by
    rw [← AddValuation.map_pow, h1, AddValuation.map_pow, hc, WithTop.coe_nsmul]
  by_cases h : v (LinearMap.det f) = ⊤
  · rw [h, exwa_nsmul_top k hk] at h2
    exact absurd h2 WithTop.top_ne_coe
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← hq] at h2 ⊢
    rw [ ← WithTop.coe_nsmul, WithTop.coe_inj] at h2
    rw [WithTop.coe_inj]
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    simp only [nsmul_eq_mul] at h2
    exact mul_left_cancel₀ hk' h2

lemma exwa_restrict_pow_coe {M : Type} [AddCommGroup M] [Module LL M] (f : M →ₗ[LL] M)
    (p : Submodule LL M) (h : ∀ x ∈ p, f x ∈ p) (k : ℕ) (x : p) :
    (((f.restrict h) ^ k) x : M) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply,
      LinearMap.coe_restrict_apply]

end ExWAVal

section ExWAMain

variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]

lemma exwaF_e (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).e = 1 := rfl

lemma exwa_finrank : finrank LL (ZMod n → LL) = n := by
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card n]

lemma exwaF_val_det (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) :
    v (LinearMap.det ((exwaF (n := n) c hc).φ : (ZMod n → LL) →ₗ[LL] (ZMod n → LL))) =
      (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
  have hcn : v (c ^ n) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]
  exact exwa_val_det v _ n (NeZero.ne n) exwa_finrank (c ^ n) _ (exwaPhi_pow_n c hc) hcn

lemma exwaF_val_det_top (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) (h : ∀ x ∈ (⊤ : Submodule LL (ZMod n → LL)),
      (exwaF (n := n) c hc).φ x ∈ (⊤ : Submodule LL (ZMod n → LL))) :
    v (LinearMap.det ((exwaF (n := n) c hc).φres ⊤ h)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
  have hcn : v (c ^ n) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]
  refine exwa_val_det v _ n (NeZero.ne n) (by rw [finrank_top, exwa_finrank]) (c ^ n) _ ?_ hcn
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [FilPhi.φres, exwa_restrict_pow_coe]
  change ((exwaPhi (n := n) c hc).toLinearMap ^ n) (x : ZMod n → LL) = _
  rw [exwaPhi_pow_n]
  simp

lemma exwa_sub_cases (c : LL) (hc : c ≠ 0) (D' : Submodule LL (ZMod n → LL))
    (hD : (exwaF c hc).IsSub D') : D' = ⊥ ∨ D' = ⊤ := by
  by_cases h : ∃ i, (Pi.single i (1 : LL) : ZMod n → LL) ∈ D'
  · right
    obtain ⟨i, hi⟩ := h
    have step : ∀ j, (Pi.single j (1 : LL) : ZMod n → LL) ∈ D' →
        (Pi.single (j + 1) (1 : LL) : ZMod n → LL) ∈ D' := by
      intro j hj
      have h1 := hD.1 _ hj
      rw [exwaF_φ, exwaPhi_single] at h1
      have h2 := D'.smul_mem c⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    have all : ∀ k : ℕ, (Pi.single (i + k) (1 : LL) : ZMod n → LL) ∈ D' := by
      intro k
      induction k with
      | zero => simpa using hi
      | succ k ih => simpa [Nat.cast_succ, add_assoc] using step _ ih
    have allj : ∀ j, (Pi.single j (1 : LL) : ZMod n → LL) ∈ D' := by
      intro j
      have h1 := all (j - i).val
      have h2 : i + (((j - i).val : ℕ) : ZMod n) = j := by
        rw [ZMod.natCast_zmod_val]; ring
      rwa [h2] at h1
    rw [eq_top_iff, ← (Pi.basisFun LL (ZMod n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simpa using allj j
  · left
    simp only [not_exists] at h
    rw [hD.2]
    refine iSup_eq_bot.mpr fun i => ?_
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    rw [exwaF_Dl] at hx2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx2
    by_cases ha : a = 0
    · simp [ha]
    · exfalso
      apply h i
      have h3 := D'.smul_mem a⁻¹ hx1
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3

lemma exwaF_WA_iff (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) : (exwaF (n := n) c hc).WeaklyAdmissible v ↔ r = -1 := by
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have key : (((exwaF (n := n) c hc).tH ⊤ : ℚ) : WithTop ℚ) =
      (exwaF (n := n) c hc).e • v (LinearMap.det ((exwaF (n := n) c hc).φ :
        (ZMod n → LL) →ₗ[LL] (ZMod n → LL))) ↔ r = -1 := by
    rw [exwaF_tH_top, exwaF_val_det v c hc r hr, exwaF_e, one_nsmul, WithTop.coe_inj]
    push_cast
    constructor
    · intro h
      have h' : (n : ℚ) * r = (n : ℚ) * (-1) := by linarith
      exact mul_left_cancel₀ hn h'
    · intro h; rw [h]; ring
  constructor
  · intro h; exact key.mp h.1
  · intro h
    refine ⟨key.mpr h, ?_⟩
    intro D' hD
    rcases exwa_sub_cases c hc D' hD with rfl | rfl
    · unfold FilPhi.NewtonAbove
      rw [exwaF_tH_bot, LinearMap.det_eq_one_of_finrank_eq_zero (finrank_bot _ _), AddValuation.map_one]
      simp
    · unfold FilPhi.NewtonAbove
      rw [exwaF_tH_top, exwaF_val_det_top v c hc r hr, exwaF_e, one_nsmul, h]
      apply le_of_eq
      rw [WithTop.coe_inj]
      push_cast
      ring

end ExWAMain

theorem exWA : ExWA := by
  intro LL _ v l hv n _
  have hl : l ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hv
    exact absurd hv (by simp)
  have hinv : v l⁻¹ = ((-1 : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_inv, hv]
    rfl
  have hone : v (1 : LL) = ((0 : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_one]
    rfl
  refine ⟨ZMod n → LL, inferInstance, inferInstance, inferInstance,
    exwaF l⁻¹ (inv_ne_zero hl), exwaF 1 one_ne_zero, ?_, ?_, ?_⟩
  · exact (exwaF_WA_iff v _ _ _ hinv).mpr rfl
  · intro τ
    unfold FilPhi.IsJump
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, exwaF_Fil_0, exwaFiltration_neg_one_eq_span_single]
    intro h
    have h2 := Submodule.span_singleton_eq_bot.mp h.symm
    simp at h2
  · rw [exwaF_WA_iff v _ _ _ hone]
    norm_num

end Formalism.WeaklyAdmissibleFiltrations
