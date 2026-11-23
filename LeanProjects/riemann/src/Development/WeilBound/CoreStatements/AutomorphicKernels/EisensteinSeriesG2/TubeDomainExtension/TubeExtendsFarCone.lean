import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.TubeDomainExtension.Statement
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.TubeDomainExtension.Lemmas

open Filter Topology MeasureTheory

namespace EisTube

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {ι : Type} [Fintype ι]

def cz (x y : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I

lemma reV_cz (x y : ι → ℝ) : reV (cz x y) = x := by
  funext i; simp [reV, cz]

lemma imV_cz (x y : ι → ℝ) : imV (cz x y) = y := by
  funext i; simp [imV, cz]

lemma cz_re_im (z : ι → ℂ) : cz (reV z) (imV z) = z := by
  funext i; simp [cz, reV, imV, Complex.re_add_im]

lemma continuous_cz_right (x : ι → ℝ) : Continuous (fun y : ι → ℝ => cz x y) := by
  unfold cz; fun_prop

lemma sum_cz_mul (x y t : ι → ℝ) :
    ∑ i, cz x y i * (t i : ℂ) =
      ((∑ i, x i * t i : ℝ) : ℂ) + ((∑ i, y i * t i : ℝ) : ℂ) * Complex.I := by
  simp only [cz, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma norm_exp_sq_cz (x y : ι → ℝ) :
    ‖Complex.exp (∑ i, cz x y i ^ 2)‖ =
      Real.exp (∑ i, x i ^ 2) * Real.exp (-∑ i, y i ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Complex.re_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cz, sq, Complex.mul_re]

noncomputable def kern (z : ι → ℂ) (t : ι → ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ i, z i * t i)

lemma norm_kern_cz (x y t : ι → ℝ) :
    ‖kern (cz x y) t‖ = Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) := by
  rw [kern, sum_cz_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

lemma kern_cz (x y t : ι → ℝ) :
    kern (cz x y) t = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) *
      Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ i, (x i : ℂ) * t i) := by
  rw [kern, ← Complex.exp_add]
  congr 1
  simp only [cz, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

lemma exp_cz_split (x y t : ι → ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * ∑ i, cz x y i * t i) =
      Complex.exp (2 * (Real.pi : ℂ) * ∑ i, ((x i : ℂ)) * t i) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (y i : ℂ) * t i) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [cz, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

lemma gauss2 : Integrable (fun y : ι → ℝ => Real.exp (-(∑ i, y i ^ 2) / 2)) := by
  have := gaussInt ι (1 / 2) (by norm_num)
  refine this.congr (ae_of_all _ fun y => ?_)
  simp only
  congr 1; ring

lemma continuous_reV : Continuous (reV : (ι → ℂ) → ι → ℝ) :=
  continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)

lemma isOpen_tube {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) :=
  hΩ.preimage continuous_reV

lemma cz_mem_tube {Ω : Set (ι → ℝ)} {x : ι → ℝ} (hx : x ∈ Ω) (y : ι → ℝ) : cz x y ∈ tube Ω := by
  show reV (cz x y) ∈ Ω
  rw [reV_cz]; exact hx

section
variable {P : Type*} [TopologicalSpace P]

noncomputable def gf (F : (ι → ℂ) → P → ℂ) (z : ι → ℂ) (p : P) : ℂ :=
  F z p * Complex.exp (∑ i, z i ^ 2)

lemma gf_bound {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {K : Set (ι → ℝ)} (hK : K ⊆ Ω) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ (y : ι → ℝ) p,
      ‖gf F (cz x y) p‖ ≤ C * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by
  obtain ⟨C, N, hC⟩ := hbd K hK hKc
  obtain ⟨M, hM⟩ := polyGaussBdd ι (1 / 2) (by norm_num) N
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  obtain ⟨S, hS⟩ : BddAbove ((fun x : ι → ℝ => ∑ i, x i ^ 2) '' K) :=
    hKc.bddAbove_image (by fun_prop)
  refine ⟨|C| * Real.exp S * M, by positivity, fun x hx y p => ?_⟩
  have hxS : ∑ i, x i ^ 2 ≤ S := hS ⟨x, hx, rfl⟩
  have hF := hC (cz x y) (by rw [reV_cz]; exact hx) p
  rw [imV_cz] at hF
  have hF' : ‖F (cz x y) p‖ ≤ |C| * h p * (1 + ‖y‖) ^ N :=
    hF.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (h0 p)) (by positivity))
  have e1 : Real.exp (-∑ i, y i ^ 2) =
      Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hB := hM y
  have hA : 0 ≤ |C| * h p := mul_nonneg (abs_nonneg _) (h0 p)
  rw [gf, norm_mul, norm_exp_sq_cz, e1]
  calc ‖F (cz x y) p‖ * (Real.exp (∑ i, x i ^ 2) *
          (Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2)))
      ≤ (|C| * h p * (1 + ‖y‖) ^ N) * (Real.exp (∑ i, x i ^ 2) *
          (Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2))) :=
        mul_le_mul_of_nonneg_right hF' (by positivity)
    _ = (|C| * h p) * Real.exp (∑ i, x i ^ 2) *
          ((1 + ‖y‖) ^ N * Real.exp (-(1 / 2 * ∑ i, y i ^ 2))) *
          Real.exp (-(∑ i, y i ^ 2) / 2) := by ring
    _ ≤ (|C| * h p) * Real.exp S * M * Real.exp (-(∑ i, y i ^ 2) / 2) := by
        gcongr
    _ = |C| * Real.exp S * M * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by ring

lemma gf_diff {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) (p : P) (t : ι → ℝ) :
    DifferentiableOn ℂ (fun z => gf F z p * kern z t) (tube Ω) := by
  unfold gf kern
  refine ((hhol p).mul ?_).mul ?_ <;> apply Differentiable.differentiableOn <;> fun_prop

lemma gf_cont {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) (p : P) {x : ι → ℝ} (hx : x ∈ Ω) :
    Continuous (fun y => gf F (cz x y) p) := by
  have : DifferentiableOn ℂ (fun z => gf F z p) (tube Ω) := by
    unfold gf
    exact (hhol p).mul (Differentiable.differentiableOn (by fun_prop))
  exact this.continuousOn.comp_continuous (continuous_cz_right x) (cz_mem_tube hx)

noncomputable def psiAt (F : (ι → ℂ) → P → ℂ) (x : ι → ℝ) (p : P) (t : ι → ℝ) : ℂ :=
  ∫ y, gf F (cz x y) p * kern (cz x y) t

lemma psi_indep {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₁ x₂ : ι → ℝ} (h₁ : x₁ ∈ Ω) (h₂ : x₂ ∈ Ω) (p : P) (t : ι → ℝ) :
    psiAt F x₁ p t = psiAt F x₂ p t := by
  refine tubeShift ι Ω hΩo hΩc (fun z => gf F z p * kern z t) (gf_diff hhol p t) ?_ x₁ h₁ x₂ h₂
  intro K hK hKc
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd hK hKc
  obtain ⟨Q, hQ⟩ : BddAbove ((fun x : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, x i * t i))) '' K) :=
    hKc.bddAbove_image (by fun_prop)
  refine ⟨C * h p * Q, fun x hx y => ?_⟩
  show ‖gf F (cz x y) p * kern (cz x y) t‖ ≤ _
  rw [norm_mul, norm_kern_cz]
  have hq : Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) ≤ Q := hQ ⟨x, hx, rfl⟩
  calc ‖gf F (cz x y) p‖ * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))
      ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * Q :=
        mul_le_mul (hC x hx y p) hq (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hC0 (h0 p)) (Real.exp_pos _).le)
    _ = C * h p * Q * Real.exp (-(∑ i, y i ^ 2) / 2) := by ring

end

section
variable {P : Type*} [TopologicalSpace P]

lemma psi_bound_at {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ x : ι → ℝ} (h₀ : x₀ ∈ Ω) (hx : x ∈ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p t, ‖psiAt F x₀ p t‖ ≤ M * h p * Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) := by
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 hx) isCompact_singleton
  have hI2 : 0 ≤ ∫ y : ι → ℝ, Real.exp (-(∑ i, y i ^ 2) / 2) :=
    integral_nonneg fun y => (Real.exp_pos _).le
  refine ⟨C * ∫ y : ι → ℝ, Real.exp (-(∑ i, y i ^ 2) / 2), mul_nonneg hC0 hI2, fun p t => ?_⟩
  rw [psi_indep hΩo hΩc h0 hhol hbd h₀ hx p t]
  have hb : ∀ y : ι → ℝ, ‖gf F (cz x y) p * kern (cz x y) t‖ ≤
      (C * h p * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))) * Real.exp (-(∑ i, y i ^ 2) / 2) :=
    fun y => by
      rw [norm_mul, norm_kern_cz]
      have := hC x (Set.mem_singleton x) y p
      calc ‖gf F (cz x y) p‖ * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))
          ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = _ := by ring
  have hn := norm_integral_le_of_norm_le (gauss2.const_mul
    (C * h p * Real.exp (-(2 * Real.pi * ∑ i, x i * t i)))) (ae_of_all _ hb)
  rw [integral_const_mul] at hn
  refine hn.trans (le_of_eq ?_)
  ring

lemma psi_bound_all {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hmid : ∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (v : ι → ℝ) :
    ∃ M : ℝ, ∀ p t, ‖psiAt F x₀ p t‖ ≤ M * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)) := by
  obtain ⟨x₁, h₁, x₂, h₂, rfl⟩ := hmid v
  obtain ⟨M₁, hM₁, hb₁⟩ := psi_bound_at hΩo hΩc h0 hhol hbd h₀ h₁
  obtain ⟨M₂, hM₂, hb₂⟩ := psi_bound_at hΩo hΩc h0 hhol hbd h₀ h₂
  refine ⟨max M₁ M₂, fun p t => ?_⟩
  have hm : ∀ i, (midpoint ℝ x₁ x₂) i = (x₁ i + x₂ i) / 2 := fun i => by
    rw [midpoint_eq_smul_add]; simp; ring
  have he : -(2 * Real.pi * ∑ i, (midpoint ℝ x₁ x₂) i * t i) =
      ((-(2 * Real.pi * ∑ i, x₁ i * t i)) + (-(2 * Real.pi * ∑ i, x₂ i * t i))) / 2 := by
    simp only [hm]
    rw [show ∑ i, (x₁ i + x₂ i) / 2 * t i = (∑ i, x₁ i * t i + ∑ i, x₂ i * t i) / 2 by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  rw [he]
  set a := -(2 * Real.pi * ∑ i, x₁ i * t i)
  set b := -(2 * Real.pi * ∑ i, x₂ i * t i)
  have hM : 0 ≤ max M₁ M₂ := le_max_of_le_left hM₁
  rcases le_total a b with hab | hab
  · calc ‖psiAt F x₀ p t‖ ≤ M₁ * h p * Real.exp a := hb₁ p t
      _ ≤ max M₁ M₂ * h p * Real.exp ((a + b) / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (h0 p))
          (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg hM (h0 p))
  · calc ‖psiAt F x₀ p t‖ ≤ M₂ * h p * Real.exp b := hb₂ p t
      _ ≤ max M₁ M₂ * h p * Real.exp ((a + b) / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (h0 p))
          (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg hM (h0 p))

lemma psi_meas {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (p : P) :
    AEStronglyMeasurable (psiAt F x₀ p) := by
  have hc : Continuous (fun q : (ι → ℝ) × (ι → ℝ) => gf F (cz x₀ q.2) p * kern (cz x₀ q.2) q.1) := by
    refine ((gf_cont hhol p h₀).comp continuous_snd).mul ?_
    unfold kern cz; fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

lemma psi_cont [FirstCountableTopology P] {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (t : ι → ℝ) :
    Continuous (fun p => psiAt F x₀ p t) := by
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 h₀) isCompact_singleton
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨U, hU, B, hB⟩ := hloc p₀
  set E := Real.exp (-(2 * Real.pi * ∑ i, x₀ i * t i))
  refine continuousAt_of_dominated (bound := fun y => (C * B * E) * Real.exp (-(∑ i, y i ^ 2) / 2))
    (Eventually.of_forall fun p => ?_) ?_ (gauss2.const_mul _) (ae_of_all _ fun y => ?_)
  · exact ((gf_cont hhol p h₀).mul (by unfold kern cz; fun_prop)).aestronglyMeasurable
  · filter_upwards [hU] with p hp
    refine ae_of_all _ fun y => ?_
    rw [norm_mul, norm_kern_cz]
    have hBp : h p ≤ B := hB ⟨p, hp, rfl⟩
    calc ‖gf F (cz x₀ y) p‖ * E ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * E :=
          mul_le_mul_of_nonneg_right (hC x₀ (Set.mem_singleton x₀) y p) (Real.exp_pos _).le
      _ ≤ (C * B * Real.exp (-(∑ i, y i ^ 2) / 2)) * E := by
          gcongr
      _ = _ := by ring
  · have : Continuous (fun p => gf F (cz x₀ y) p) := by
      unfold gf
      exact (hcont _ (cz_mem_tube h₀ y)).mul continuous_const
    exact (this.mul continuous_const).continuousAt

end

section
variable {P : Type*} [TopologicalSpace P]

lemma lap_eq {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ x : ι → ℝ} (h₀ : x₀ ∈ Ω) (hx : x ∈ Ω) (p : P) (y : ι → ℝ)
    (Lint : ∀ (z : ι → ℂ), Integrable
        (fun t : ι → ℝ => psiAt F x₀ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) :
    (∫ t : ι → ℝ, psiAt F x₀ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, cz x y i * t i)) =
      gf F (cz x y) p := by
  have hgc : Continuous (fun y' => gf F (cz x y') p) := gf_cont hhol p hx
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 hx) isCompact_singleton
  have hgi : Integrable (fun y' => gf F (cz x y') p) :=
    (gauss2.const_mul (C * h p)).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun y' => hC x (Set.mem_singleton x) y' p)
  have hhat : ∀ t : ι → ℝ, (∫ y', gf F (cz x y') p *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) =
      psiAt F x₀ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, (x i : ℂ) * t i) := by
    intro t
    rw [psi_indep hΩo hΩc h0 hhol hbd h₀ hx p t, psiAt]
    simp_rw [kern_cz, ← mul_assoc]
    rw [integral_mul_const]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
  have hhati : Integrable (fun t : ι → ℝ => ∫ y', gf F (cz x y') p *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) :=
    (Lint (fun i => (x i : ℂ))).congr (ae_of_all _ fun t => (hhat t).symm)
  have inv := fourierInvCoord ι (fun y' => gf F (cz x y') p) hgc hgi hhati y
  refine (integral_congr_ae (ae_of_all _ fun t => ?_)).trans inv
  rw [hhat t, exp_cz_split]
  ring

end

theorem tubeExtends (P : Type*) [TopologicalSpace P] [FirstCountableTopology P] :
    TubeExtends (ι := ι) P := by
  intro Ω hΩo hΩc hmid h h0 hloc F hhol hcont hbd
  obtain ⟨x₀, h₀, -, -, -⟩ := hmid 0
  obtain ⟨Lint, Ldiff, Lcont, Lbd⟩ := laplaceEntire ι P h h0 hloc (psiAt F x₀)
    (psi_meas hhol h₀) (psi_cont h0 hloc hhol hcont hbd h₀)
    (psi_bound_all hΩo hΩc hmid h0 hhol hbd h₀)
  refine ⟨fun z p => (∫ t : ι → ℝ, psiAt F x₀ p t *
      Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)) * Complex.exp (-∑ i, z i ^ 2),
    fun p => (Ldiff p).mul (by fun_prop), ?_, ?_, ?_⟩
  · intro z hz p
    have hx : reV z ∈ Ω := hz
    beta_reduce
    rw [← cz_re_im z, lap_eq hΩo hΩc h0 hhol hbd h₀ hx p (imV z) (Lint p), gf, mul_assoc,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  · exact Lcont.mul (by fun_prop)
  · intro K hK
    obtain ⟨C, hC⟩ := Lbd K hK
    obtain ⟨Q, hQ⟩ : BddAbove ((fun z : ι → ℂ => ‖Complex.exp (-∑ i, z i ^ 2)‖) '' K) :=
      hK.bddAbove_image (by fun_prop)
    refine ⟨C * Q, fun z hz p => ?_⟩
    rw [norm_mul]
    have h1 := hC z hz p
    have h2 : ‖Complex.exp (-∑ i, z i ^ 2)‖ ≤ Q := hQ ⟨z, hz, rfl⟩
    calc _ ≤ (C * h p) * Q := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = C * Q * h p := by ring

theorem tubeExtends_farCone {J : Type*} [Fintype J]
    (P : Type*) [TopologicalSpace P] [FirstCountableTopology P]
    (a : J → ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hne : (farCone a R).Nonempty)
    (Ω : Set (ι → ℝ)) (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hpos : farCone a R ⊆ Ω) (hneg : ∀ x ∈ farCone a R, -x ∈ Ω)
    (h : P → ℝ) (h0 : ∀ p, 0 ≤ h p) (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U))
    (F : (ι → ℂ) → P → ℂ)
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) :
    ∃ G : (ι → ℂ) → P → ℂ,
      (∀ p, Differentiable ℂ (fun z => G z p)) ∧
      (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
      Continuous (Function.uncurry G) ∧
      (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p) := by
  refine tubeExtends P Ω hΩo hΩc ?_ h h0 hloc F hhol hcont hbd
  intro v
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : ∀ j, 0 < ∑ i, x₀ i * a j i := fun j => lt_of_le_of_lt hR (hx₀ j)
  set s : ℝ := 1 + ∑ j, (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i with hs
  have key : ∀ j, R + |∑ i, v i * a j i| < s * ∑ i, x₀ i * a j i := by
    intro j
    have hle : (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i ≤
        ∑ j, (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i :=
      Finset.single_le_sum (f := fun j => (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i)
        (fun j _ => div_nonneg (add_nonneg hR (abs_nonneg _)) (hd j).le) (Finset.mem_univ j)
    have h1 : (1 + (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i) * ∑ i, x₀ i * a j i ≤
        s * ∑ i, x₀ i * a j i :=
      mul_le_mul_of_nonneg_right (by rw [hs]; linarith) (hd j).le
    rw [add_mul, one_mul, div_mul_cancel₀ _ (hd j).ne'] at h1
    linarith [hd j]
  have hsum : ∀ (u w : ι → ℝ) (c : ℝ) j,
      ∑ i, (u + c • w) i * a j i = ∑ i, u i * a j i + c * ∑ i, w i * a j i := by
    intro u w c j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have m1 : v + s • x₀ ∈ farCone a R := fun j => by
    rw [hsum]; linarith [key j, neg_abs_le (∑ i, v i * a j i)]
  have m2 : -v + s • x₀ ∈ farCone a R := fun j => by
    rw [hsum]
    have : ∑ i, (-v) i * a j i = -∑ i, v i * a j i := by
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [this]; linarith [key j, le_abs_self (∑ i, v i * a j i)]
  refine ⟨v + s • x₀, hpos m1, -(-v + s • x₀), hneg _ m2, ?_⟩
  funext i
  simp [midpoint_eq_smul_add]
  ring

end EisTube
