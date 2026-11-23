import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevMultiplication

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def HasOrder (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (k : ℝ) : Prop :=
  ∀ s : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : 𝓢'(E, ℂ), MemSobolev s 2 u →
    sob (s - k) (T u) ≤ ENNReal.ofReal C * sob s u

namespace HasOrder

variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {k k₁ k₂ : ℝ}

theorem memSobolev (h : HasOrder T k) {s : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    MemSobolev (s - k) 2 (T u) := by
  obtain ⟨C, -, hC⟩ := h s
  exact memSobolev_of_sob_le ENNReal.ofReal_ne_top (hC u hu) hu

theorem memSobolev' (h : HasOrder T k) {s t : ℝ} (hst : t = s - k) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) : MemSobolev t 2 (T u) := by
  subst hst; exact h.memSobolev hu

theorem mono (h : HasOrder T k) {k' : ℝ} (hk : k ≤ k') : HasOrder T k' := by
  intro s
  obtain ⟨C, hC0, hC⟩ := h s
  exact ⟨C, hC0, fun u hu ↦ (sob_mono (by linarith) _).trans (hC u hu)⟩

theorem add (h₁ : HasOrder T₁ k) (h₂ : HasOrder T₂ k) : HasOrder (T₁ + T₂) k := by
  intro s
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ s
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ s
  refine ⟨C₁ + C₂, by positivity, fun u hu ↦ ?_⟩
  rw [add_apply, ENNReal.ofReal_add hC₁0 hC₂0, add_mul]
  exact (sob_add_le _ _).trans (add_le_add (hC₁ u hu) (hC₂ u hu))

theorem smul (h : HasOrder T k) (c : ℂ) : HasOrder (c • T) k := by
  intro s
  obtain ⟨C, hC0, hC⟩ := h s
  refine ⟨‖c‖ * C, by positivity, fun u hu ↦ ?_⟩
  rw [smul_apply, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, mul_assoc]
  exact (sob_smul_le _ _).trans (mul_le_mul_right (hC u hu) _)

theorem neg (h : HasOrder T k) : HasOrder (-T) k := by
  simpa using h.smul (-1)

theorem sub (h₁ : HasOrder T₁ k) (h₂ : HasOrder T₂ k) : HasOrder (T₁ - T₂) k := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

theorem zero (k : ℝ) : HasOrder (0 : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) k :=
  fun _ ↦ ⟨0, le_rfl, fun u _ ↦ by simp [sob_zero]⟩

theorem id : HasOrder (ContinuousLinearMap.id ℂ 𝓢'(E, ℂ)) 0 :=
  fun s ↦ ⟨1, zero_le_one, fun u _ ↦ by simp⟩

theorem comp (h₁ : HasOrder T₁ k₁) (h₂ : HasOrder T₂ k₂) : HasOrder (T₁ ∘L T₂) (k₁ + k₂) := by
  intro s
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ s
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ (s - k₂)
  refine ⟨C₁ * C₂, by positivity, fun u hu ↦ ?_⟩
  have hmem := h₂.memSobolev hu
  rw [ContinuousLinearMap.comp_apply, sob_congr (show s - (k₁ + k₂) = s - k₂ - k₁ by ring),
    ENNReal.ofReal_mul hC₁0, mul_assoc]
  exact (hC₁ _ hmem).trans (mul_le_mul_right (hC₂ u hu) _)

theorem sum {ι : Type*} (S : Finset ι) {T : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (h : ∀ i ∈ S, HasOrder (T i) k) : HasOrder (∑ i ∈ S, T i) k := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using zero k
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end HasOrder

theorem hasOrder_smulLeft (χ : 𝓢(E, ℂ)) : HasOrder (smulLeftCLM ℂ (χ : E → ℂ)) 0 := fun s ↦
  ⟨mulConst s χ, mulConst_nonneg s χ, fun u hu ↦ by
    rw [sub_zero]; exact sob_smulLeft_le χ s hu⟩

theorem hasOrder_mulRem (χ : 𝓢(E, ℂ)) (r : ℝ) : HasOrder (mulRem χ r) (-1) := fun s ↦
  ⟨commConst r (s + 1 - r) * wInt ((|s + 1 - r| + |r - 1| + 1) / 2) (𝓕 χ),
    mul_nonneg (commConst_nonneg _ _) (wInt_nonneg _ _), fun u hu ↦ by
    have h := sob_mulRem_le χ r (s + 1 - r) (u := u) (by convert hu using 2; ring)
    rwa [show r + (s + 1 - r) = s - -1 by ring, show s - -1 - 1 = s by ring] at h⟩

theorem hasOrder_lineDeriv (v : E) : HasOrder (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v) 1 := fun s ↦
  ⟨2 * Real.pi * ‖v‖, by positivity, fun u hu ↦ sob_lineDeriv_le v hu⟩

theorem hasOrder_iteratedLineDeriv {k : ℕ} (w : Fin k → E) :
    HasOrder (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) k := by
  induction k with
  | zero =>
    have : iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w = ContinuousLinearMap.id ℂ _ := by
      ext1 u; simp
    rw [this]; simpa using HasOrder.id
  | succ k ih =>
    have : iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w =
        lineDerivOpCLM ℂ 𝓢'(E, ℂ) (w 0) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (Fin.tail w) := by
      ext1 u; simp [iteratedLineDerivOp_succ_left]
    rw [this]
    have h := (hasOrder_lineDeriv (w 0)).comp (ih (Fin.tail w))
    rwa [show (1 : ℝ) + k = ((k + 1 : ℕ) : ℝ) by push_cast; ring] at h

def IsLocal (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) : Prop :=
  ∀ U : Set E, IsOpen U → ∀ u : 𝓢'(E, ℂ), Distribution.IsVanishingOn u U →
    Distribution.IsVanishingOn (T u) U

theorem isVanishingOn_add {u v : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U)
    (hv : Distribution.IsVanishingOn v U) : Distribution.IsVanishingOn (u + v) U := fun φ hφ ↦ by
  rw [add_apply, hu φ hφ, hv φ hφ, add_zero]

theorem isVanishingOn_smul {u : 𝓢'(E, ℂ)} {U : Set E} (c : ℂ) (hu : Distribution.IsVanishingOn u U) :
    Distribution.IsVanishingOn (c • u) U := fun φ hφ ↦ by
  rw [smul_apply, hu φ hφ, smul_zero]

theorem isVanishingOn_neg {u : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U) :
    Distribution.IsVanishingOn (-u) U := fun φ hφ ↦ by
  rw [neg_apply, hu φ hφ, neg_zero]

theorem isVanishingOn_sub {u v : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U)
    (hv : Distribution.IsVanishingOn v U) : Distribution.IsVanishingOn (u - v) U := by
  rw [sub_eq_add_neg]; exact isVanishingOn_add hu (isVanishingOn_neg hv)

theorem isVanishingOn_zero (U : Set E) : Distribution.IsVanishingOn (0 : 𝓢'(E, ℂ)) U :=
  fun _ _ ↦ rfl

namespace IsLocal

variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}

theorem add (h₁ : IsLocal T₁) (h₂ : IsLocal T₂) : IsLocal (T₁ + T₂) := fun U hU u hu ↦ by
  rw [add_apply]; exact isVanishingOn_add (h₁ U hU u hu) (h₂ U hU u hu)

theorem sub (h₁ : IsLocal T₁) (h₂ : IsLocal T₂) : IsLocal (T₁ - T₂) := fun U hU u hu ↦ by
  rw [sub_apply]; exact isVanishingOn_sub (h₁ U hU u hu) (h₂ U hU u hu)

theorem smul (h : IsLocal T) (c : ℂ) : IsLocal (c • T) := fun U hU u hu ↦ by
  rw [smul_apply]; exact isVanishingOn_smul c (h U hU u hu)

theorem comp (h₁ : IsLocal T₁) (h₂ : IsLocal T₂) : IsLocal (T₁ ∘L T₂) := fun U hU u hu ↦
  h₁ U hU _ (h₂ U hU u hu)

theorem zero : IsLocal (0 : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) := fun U _ _ _ ↦ isVanishingOn_zero U

theorem id : IsLocal (ContinuousLinearMap.id ℂ 𝓢'(E, ℂ)) := fun _ _ _ hu ↦ hu

theorem sum {ι : Type*} (S : Finset ι) {T : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (h : ∀ i ∈ S, IsLocal (T i)) : IsLocal (∑ i ∈ S, T i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using zero
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end IsLocal

theorem isLocal_smulLeft {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    IsLocal (smulLeftCLM ℂ g) := fun _ _ _ hu ↦
  Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hu hg

theorem isLocal_iteratedLineDeriv {k : ℕ} (w : Fin k → E) :
    IsLocal (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) := fun _ _ _ hu ↦
  Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp hu w

theorem smulLeftCLM_eq_zero_of_isVanishingOn {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {u : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U) (hgU : tsupport g ⊆ U) :
    smulLeftCLM ℂ g u = 0 := by
  ext φ
  rw [smulLeftCLM_apply_apply, zero_apply]
  apply hu
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_left g φ).trans hgU

theorem isVanishingOn_smulLeftCLM_sub {g : E → ℂ} (hg : g.HasTemperateGrowth) {V : Set E}
    (hgV : ∀ x ∈ V, g x = 1) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn (smulLeftCLM ℂ g u - u) V := by
  intro φ hφ
  rw [sub_apply, smulLeftCLM_apply_apply, sub_eq_zero]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  by_cases hx : φ x = 0
  · rw [hx, mul_zero]
  · rw [hgV x (hφ (subset_tsupport φ hx)), one_mul]

theorem isVanishingOn_smulLeftCLM_compl {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn (smulLeftCLM ℂ g u) (tsupport g)ᶜ := by
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  have : SchwartzMap.smulLeftCLM ℂ g φ = 0 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, zero_apply]
    by_cases hx : x ∈ tsupport g
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hφ h hx), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [this, map_zero]

theorem lineDerivOp_smulLeftCLM_schwartz (v : E) (ψ φ : 𝓢(E, ℂ)) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) φ) =
      SchwartzMap.smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) φ +
        SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) (∂_{v} φ) := by
  ext x
  have hψ := ψ.hasTemperateGrowth
  have hψ' := (∂_{v} ψ : 𝓢(E, ℂ)).hasTemperateGrowth
  rw [add_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply_apply hψ', SchwartzMap.smulLeftCLM_apply_apply hψ,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have e : ⇑(SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) φ) = fun y ↦ ψ y * φ y := by
    ext y; rw [SchwartzMap.smulLeftCLM_apply_apply hψ, smul_eq_mul]
  rw [e, fderiv_fun_mul (ψ.differentiableAt) (φ.differentiableAt)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem lineDerivOp_smulLeftCLM (v : E) (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (smulLeftCLM ℂ (ψ : E → ℂ) u) =
      smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) u + smulLeftCLM ℂ (ψ : E → ℂ) (∂_{v} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply_apply, add_apply, map_neg]
  rw [lineDerivOp_smulLeftCLM_schwartz, map_add]
  ring

def comm (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  T ∘L smulLeftCLM ℂ (ψ : E → ℂ) - smulLeftCLM ℂ (ψ : E → ℂ) ∘L T

theorem comm_apply (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    comm T ψ u = T (smulLeftCLM ℂ (ψ : E → ℂ) u) - smulLeftCLM ℂ (ψ : E → ℂ) (T u) := rfl

theorem comm_lineDeriv (v : E) (ψ : 𝓢(E, ℂ)) :
    comm (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v) ψ = smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) := by
  ext1 u
  rw [comm_apply, lineDerivOpCLM_apply, lineDerivOpCLM_apply, lineDerivOp_smulLeftCLM]
  abel

theorem comm_comp (A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) :
    comm (A ∘L B) ψ = A ∘L comm B ψ + comm A ψ ∘L B := by
  ext1 u
  simp only [comm_apply, ContinuousLinearMap.comp_apply, add_apply, map_sub]
  abel

theorem comm_smulLeft_comp {g : E → ℂ} (hg : g.HasTemperateGrowth) (A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (ψ : 𝓢(E, ℂ)) : comm (smulLeftCLM ℂ g ∘L A) ψ = smulLeftCLM ℂ g ∘L comm A ψ := by
  ext1 u
  simp only [comm_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth hg,
    smulLeftCLM_smulLeftCLM_apply hg ψ.hasTemperateGrowth, mul_comm]

theorem comm_add (A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) :
    comm (A + B) ψ = comm A ψ + comm B ψ := by
  ext1 u; simp only [comm_apply, add_apply, map_add]; abel

theorem comm_sum {ι : Type*} (S : Finset ι) (A : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) :
    comm (∑ i ∈ S, A i) ψ = ∑ i ∈ S, comm (A i) ψ := by
  classical
  induction S using Finset.induction_on with
  | empty => ext1 u; simp [comm_apply]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comm_add, ih]

theorem hasOrder_comm_iteratedLineDeriv {k : ℕ} (w : Fin k → E) (ψ : 𝓢(E, ℂ)) :
    HasOrder (comm (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) ψ) (k - 1) := by
  induction k with
  | zero =>
    have : comm (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) ψ = 0 := by
      ext1 u; simp [comm_apply]
    rw [this]; exact HasOrder.zero _
  | succ k ih =>
    have e : iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w =
        lineDerivOpCLM ℂ 𝓢'(E, ℂ) (w 0) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (Fin.tail w) := by
      ext1 u; simp [iteratedLineDerivOp_succ_left]
    rw [e, comm_comp, comm_lineDeriv]
    have h1 := (hasOrder_lineDeriv (E := E) (w 0)).comp (ih (Fin.tail w))
    have h2 := (hasOrder_smulLeft (∂_{w 0} ψ : 𝓢(E, ℂ))).comp
      (hasOrder_iteratedLineDeriv (E := E) (Fin.tail w))
    refine (h1.mono (le_of_eq ?_)).add (h2.mono (le_of_eq ?_)) <;> push_cast <;> ring

def derivSymb {k : ℕ} (w : Fin k → E) (ξ : E) : ℂ :=
  ∏ j, (2 * Real.pi * Complex.I) * ((inner ℝ ξ (w j) : ℝ) : ℂ)

theorem derivSymb_succ {k : ℕ} (w : Fin (k + 1) → E) (ξ : E) :
    derivSymb w ξ = derivSymb (Fin.tail w) ξ * ((2 * Real.pi * Complex.I) * ((inner ℝ ξ (w 0) : ℝ) : ℂ)) := by
  rw [derivSymb, Fin.prod_univ_succ, mul_comm]; rfl

theorem derivSymb_hasTemperateGrowth {k : ℕ} (w : Fin k → E) : (derivSymb w).HasTemperateGrowth := by
  induction k with
  | zero =>
    have : derivSymb w = fun _ ↦ 1 := by ext ξ; simp [derivSymb]
    rw [this]; exact Function.HasTemperateGrowth.const 1
  | succ k ih =>
    have : derivSymb w = fun ξ ↦ derivSymb (Fin.tail w) ξ *
        ((2 * Real.pi * Complex.I) * ((inner ℝ ξ (w 0) : ℝ) : ℂ)) := by
      ext ξ; exact derivSymb_succ w ξ
    rw [this]
    exact (ih _).mul (by fun_prop)

theorem norm_derivSymb_le {k : ℕ} (w : Fin k → E) (ξ : E) :
    ‖derivSymb w ξ‖ ≤ (∏ j, (2 * Real.pi * ‖w j‖)) * ‖ξ‖ ^ k := by
  rw [derivSymb, norm_prod, ← Fin.prod_const k ‖ξ‖, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun j _ ↦ norm_nonneg _) fun j _ ↦ ?_
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos, h2]
  calc 2 * Real.pi * |inner ℝ ξ (w j)| ≤ 2 * Real.pi * (‖ξ‖ * ‖w j‖) := by
        gcongr; exact abs_real_inner_le_norm ξ (w j)
    _ = _ := by ring

theorem iteratedLineDeriv_eq_fourierMultiplier {k : ℕ} (w : Fin k → E) (u : 𝓢'(E, ℂ)) :
    ∂^{w} u = fourierMultiplierCLM ℂ (derivSymb w) u := by
  induction k generalizing u with
  | zero =>
    have : derivSymb w = fun _ ↦ 1 := by ext ξ; simp [derivSymb]
    rw [this, fourierMultiplierCLM_const]; simp
  | succ k ih =>
    have hg : (fun x : E ↦ ((inner ℝ x (w 0) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
    rw [iteratedLineDerivOp_succ_left, ih, lineDeriv_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_fourierMultiplierCLM_apply (derivSymb_hasTemperateGrowth _) hg,
      ← smul_apply, ← fourierMultiplierCLM_smul ((derivSymb_hasTemperateGrowth _).mul hg)]
    congr 2
    ext ξ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [derivSymb_succ]; ring

def prinSymb {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) : ℂ :=
  ∑ i, c i * ∏ j, ((inner ℝ ξ (w i j) : ℝ) : ℂ)

theorem continuous_prinSymb {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) :
    Continuous (prinSymb c w) := by
  unfold prinSymb; fun_prop

theorem prinSymb_smul {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (t : ℝ)
    (ξ : E) : prinSymb c w (t • ξ) = (t : ℂ) ^ m * prinSymb c w ξ := by
  simp only [prinSymb, inner_smul_left, Finset.mul_sum]
  congr 1; ext i
  simp only [RCLike.conj_to_real, Complex.ofReal_mul, Finset.prod_mul_distrib, Fin.prod_const]
  ring

theorem derivSymb_eq {k : ℕ} (w : Fin k → E) (ξ : E) :
    derivSymb w ξ = (2 * Real.pi * Complex.I) ^ k * ∏ j, ((inner ℝ ξ (w j) : ℝ) : ℂ) := by
  rw [derivSymb, Finset.prod_mul_distrib, Fin.prod_const]

theorem norm_prinSymb_le {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) :
    ‖prinSymb c w ξ‖ ≤ (∑ i, ‖c i‖ * ∏ j, ‖w i j‖) * ‖ξ‖ ^ m := by
  rw [prinSymb, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_mul, norm_prod, mul_assoc, ← Fin.prod_const m ‖ξ‖, ← Finset.prod_mul_distrib]
  gcongr with j
  rw [Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact abs_real_inner_le_norm ξ (w i j)

theorem exists_pos_le_norm_prinSymb {ι : Type*} [Fintype ι] {m : ℕ} (hm : 1 ≤ m) (c : ι → ℂ)
    (w : ι → Fin m → E) (hell : ∀ ξ : E, ξ ≠ 0 → prinSymb c w ξ ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : E, c₀ * ‖ξ‖ ^ m ≤ ‖prinSymb c w ξ‖ := by
  by_cases hE : ∃ ξ : E, ξ ≠ 0
  · obtain ⟨ξ₀, hξ₀⟩ := hE
    have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨‖ξ₀‖⁻¹ • ξ₀, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ₀)]⟩
    obtain ⟨η, hη, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      (continuous_prinSymb c w).norm.continuousOn
    have hη0 : η ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hη; exact zero_ne_one hη
    refine ⟨‖prinSymb c w η‖, norm_pos_iff.2 (hell η hη0), fun ξ ↦ ?_⟩
    by_cases hξ : ξ = 0
    · rw [hξ, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hmem : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hmin hmem
      simp only at h1
      have h2 : prinSymb c w ξ = ((‖ξ‖ : ℝ) : ℂ) ^ m * prinSymb c w (‖ξ‖⁻¹ • ξ) := by
        rw [← prinSymb_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, mul_comm]
      gcongr
      exact h1
  · simp only [not_exists, not_not] at hE
    refine ⟨1, one_pos, fun ξ ↦ ?_⟩
    rw [hE ξ, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _

def prinOp {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E) :
    𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  ∑ i, smulLeftCLM ℂ (a i : E → ℂ) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)

section prinOp

variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)

theorem isLocal_prinOp : IsLocal (prinOp a w) :=
  IsLocal.sum _ fun i _ ↦ (isLocal_smulLeft (a i).hasTemperateGrowth).comp
    (isLocal_iteratedLineDeriv (w i))

theorem hasOrder_comm_prinOp (ψ : 𝓢(E, ℂ)) : HasOrder (comm (prinOp a w) ψ) ((m : ℝ) - 1) := by
  rw [prinOp, comm_sum]
  refine HasOrder.sum _ fun i _ ↦ ?_
  rw [comm_smulLeft_comp (a i).hasTemperateGrowth]
  simpa using (hasOrder_smulLeft (a i)).comp (hasOrder_comm_iteratedLineDeriv (w i) ψ)

def constOp (c : ι → ℂ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  ∑ i, c i • iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)

theorem constSymb_hasTemperateGrowth (c : ι → ℂ) :
    (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ).HasTemperateGrowth := by
  have : (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) =
      fun ξ ↦ ∑ i, c i * derivSymb (w i) ξ := by
    ext ξ; simp only [prinSymb, derivSymb_eq, Finset.mul_sum]; congr 1; ext i; ring
  rw [this]
  exact Function.HasTemperateGrowth.sum fun i _ ↦
    (Function.HasTemperateGrowth.const (c i)).mul (derivSymb_hasTemperateGrowth (w i))

theorem constOp_eq_fourierMultiplier (c : ι → ℂ) :
    constOp w c = fourierMultiplierCLM ℂ (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) := by
  have this : (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) =
      fun ξ ↦ ∑ i, c i * derivSymb (w i) ξ := by
    ext ξ; simp only [prinSymb, derivSymb_eq, Finset.mul_sum]
    congr 1; ext i; ring
  have hsum := fourierMultiplierCLM_sum ℂ (E := E) (g := fun i η ↦ c i * derivSymb (w i) η)
    (s := Finset.univ) (fun i _ ↦
      (Function.HasTemperateGrowth.const (c i)).mul (derivSymb_hasTemperateGrowth (w i)))
  beta_reduce at hsum
  rw [this, hsum]
  unfold constOp
  congr 1; ext1 i
  ext1 u
  rw [smul_apply, iteratedLineDerivOpCLM_apply, iteratedLineDeriv_eq_fourierMultiplier,
    show (fun η ↦ c i * derivSymb (w i) η) = c i • derivSymb (w i) from rfl,
    fourierMultiplierCLM_smul (derivSymb_hasTemperateGrowth (w i)), smul_apply]

end prinOp

def IsEllipticAt (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (m : ℕ) (x₀ : E) : Prop :=
  ∃ (n : ℕ) (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)),
    T = prinOp a w + N ∧ HasOrder N ((m : ℝ) - 1) ∧ IsLocal N ∧
      ∀ ξ : E, ξ ≠ 0 → prinSymb (fun i ↦ a i x₀) w ξ ≠ 0

namespace IsEllipticAt

variable {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}

theorem isLocal (h : IsEllipticAt T m x₀) : IsLocal T := by
  obtain ⟨n, a, w, N, rfl, -, hN, -⟩ := h
  exact (isLocal_prinOp a w).add hN

theorem hasOrder_comm (h : IsEllipticAt T m x₀) (ψ : 𝓢(E, ℂ)) : HasOrder (comm T ψ) ((m : ℝ) - 1) := by
  obtain ⟨n, a, w, N, rfl, hN, -, -⟩ := h
  rw [comm_add]
  refine (hasOrder_comm_prinOp a w ψ).add ?_
  have h1 := (hN.comp (hasOrder_smulLeft ψ)).mono (le_of_eq (add_zero _))
  have h2 := ((hasOrder_smulLeft ψ).comp hN).mono (le_of_eq (zero_add _))
  exact h1.sub h2

theorem add (h : IsEllipticAt T m x₀) {N' : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (hN' : HasOrder N' ((m : ℝ) - 1)) (hL : IsLocal N') : IsEllipticAt (T + N') m x₀ := by
  obtain ⟨n, a, w, N, rfl, hN, hNl, hell⟩ := h
  exact ⟨n, a, w, N + N', by rw [add_assoc], hN.add hN', hNl.add hL, hell⟩

end IsEllipticAt

end

end GroundTheory.Automorphic.Sobolev
