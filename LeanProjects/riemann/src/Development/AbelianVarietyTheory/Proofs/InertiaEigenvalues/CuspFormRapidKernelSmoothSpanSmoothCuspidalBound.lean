import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedContinuousCuspidalAutomorphicZeroAddSmuStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmoothStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalArchimedeanKernelConvolutionOperatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOneStatement

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem mspanR_rt {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_kerOp {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    kerOp ν k γ F ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk

theorem word_nil (φ : Sm E a) : GlobalTheory.GLFin.word [] φ = φ := by simp [GlobalTheory.GLFin.word]

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by simp [GlobalTheory.GLFin.word]

theorem word_append (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.map_append, List.prod_append]

theorem word_single (X : Lie E a) (φ : Sm E a) : GlobalTheory.GLFin.word [X] φ = lie E a X φ := by simp [GlobalTheory.GLFin.word]

def adH (h : GA E a) (X : Lie E a) : Lie E a :=
  toL ((GeneralLinearGroup.map (pInf E) h)⁻¹.val * Matrix.of X * (GeneralLinearGroup.map (pInf E) h).val)

theorem lie_rt (h : GA E a) (X : Lie E a) (φ : Sm E a) :
    lie E a X (rt E a h φ) = rt E a h (lie E a (adH h X) φ) := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have eh : h = infGL E a y * finGL E a k := (infGL_mul_finGL h).symm
  have e1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e2 : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e2] at e1
  have e3 := lie_rt_fin (adH h X) k
  have key : lie E a X * rt E a h = rt E a h * lie E a (adH h X) := by
    have e4 : rt E a h = rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [← map_mul, ← eh]
    rw [e4, ← mul_assoc, ← e1, mul_assoc]
    change _ * (lie E a (adH h X) * _) = _
    rw [e3, ← mul_assoc]
  exact LinearMap.congr_fun key φ

theorem word_rt (h : GA E a) : ∀ (l : List (Lie E a)) (φ : Sm E a),
    GlobalTheory.GLFin.word l (rt E a h φ) = rt E a h (GlobalTheory.GLFin.word (l.map (adH h)) φ)
  | [], φ => by simp [GlobalTheory.GLFin.word]
  | X :: l, φ => by rw [word_cons, word_rt h l, lie_rt, List.map_cons, word_cons]

variable (E a) in

def bccSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsBCC F}
  zero_mem' := (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).1
  add_mem' {F G} hF hG := by simpa using (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).2 1 F G hF hG
  smul_mem' c F hF := by simpa using (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).2 c F 0 hF (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).1

def dSub (π : CuspSub E a) : Submodule ℂ (Sm E a) :=
  ⨅ l : List (Lie E a), (mspanR π ⊓ bccSub E a).comap ((Sm E a).subtype ∘ₗ GlobalTheory.GLFin.word l)

theorem mem_dSub {π : CuspSub E a} {φ : Sm E a} :
    φ ∈ dSub π ↔ ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  simp only [dSub, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_inf, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rfl

theorem lie_mem_dSub {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ dSub π) (X : Lie E a) : lie E a X φ ∈ dSub π :=
  mem_dSub.2 fun l => by rw [← word_append]; exact mem_dSub.1 h _

theorem isBCC_rt {F : GA E a → ℂ} (hF : IsBCC F) (h : GA E a) : IsBCC (fun g => F (g * h)) where
  cont := hF.cont.comp (continuous_mul_right h)
  bdd := let ⟨C, hC⟩ := hF.bdd; ⟨C, fun g => hC _⟩
  cusp := by
    intro r h0 h1 _ _ μ 𝓕 hμ hF' g
    simpa only [mul_assoc] using hF.cusp r h0 h1 μ 𝓕 hμ hF' (g * h)
  left γ g := by simpa only [mul_assoc] using hF.left γ (g * h)

theorem rt_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) (h : GA E a) : rt E a h φ ∈ dSub π :=
  mem_dSub.2 fun l => by
    rw [word_rt]
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ (l.map (adH h))
    exact ⟨mspanR_rt h1 h, isBCC_rt h2 h⟩

theorem isBCC_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : IsBCC φ.1 where
  cont := (π.cusp φ h).1.continuous
  bdd := hB.of_isUnitary hπ h
  cusp := (π.cusp φ h).2
  left := (π.cusp φ h).1.left

theorem word_mem (π : CuspSub E a) : ∀ (l : List (Lie E a)) {φ : Sm E a}, φ ∈ π.V → GlobalTheory.GLFin.word l φ ∈ π.V
  | [], _, h => by rw [word_nil]; exact h
  | X :: l, _, h => by rw [word_cons]; exact π.stable (.lie X) _ (word_mem π l h)

theorem mem_dSub_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : φ ∈ dSub π :=
  mem_dSub.2 fun l => ⟨mem_mspanR_of_mem (word_mem π l h), isBCC_of_mem hB hπ (word_mem π l h)⟩

theorem isBCC_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : IsBCC φ.1) :
    IsBCC (kerOp ν k γ φ.1) where
  cont := (GlobalTheory.T.kernelOperator_integrable_continuous_smooth E a X ν k γ hk φ hφ.cont hφ.bdd).2
  bdd := by
    obtain ⟨C, hC⟩ := hφ.bdd
    have hi : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
    refine ⟨C * ∫ x, ‖k x‖ ∂ν, fun g => ?_⟩
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  cusp := GlobalTheory.T.isCuspidal_archimedeanKernelConvolutionOperator E a X ν k γ hk φ hφ
  left γ' g := by simp only [kerOp, mul_assoc, hφ.left]

theorem hasFDerivAt_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (hk : IsRapidInf ν k γ) (φ : Sm E a) (hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2)
      (oneL E a) := by
  rw [← GlobalTheory.T.integral_fderiv_realLieChart_eq_sum_kernelOperators E a X ν k γ hk φ hd g]
  exact GlobalTheory.T.hasFDerivAt_realLieChart_kernelOperator_at_one E a X ν k γ hk φ hb hd g

theorem kerOp_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    ∃ ψ ∈ dSub π, ψ.1 = kerOp ν k γ φ.1 := by
  let K : Set (GA E a → ℂ) := {f | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (φ : Sm E a), IsRapidInf ν k γ ∧ φ ∈ dSub π ∧ f = kerOp ν k γ φ.1}
  have hder : ∀ f ∈ K, ∃ fs : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a)) → GA E a → ℂ,
      (∀ p, fs p ∈ K) ∧ ∀ g, HasFDerivAt (chart f g) (∑ p, fs p g • lieCoord E a p.2) (oneL E a) := by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    have hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by simpa [word_nil] using (mem_dSub.1 hφ []).2.bdd
    have hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C := fun i => by
      simpa [word_single] using (mem_dSub.1 hφ [lieBasis E a i]).2.bdd
    exact ⟨fun p => kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1,
      fun p => ⟨X, _, ν, inferInstance, _, γ, _, GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient E a X ν k γ hk p, lie_mem_dSub hφ _, rfl⟩,
      hasFDerivAt_kerOp ν k γ hk φ hb hd⟩
  have hSm : ∀ f ∈ K, f ∈ Sm E a := GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity E a K fun f hf => by
    obtain ⟨fs, h1, h2⟩ := hder f hf
    exact ⟨_, inferInstance, fs, fun p => lieCoord E a p.2, h1, h2⟩
  have hspan : Submodule.span ℂ K ≤ Sm E a := Submodule.span_le.2 hSm
  have hlie : ∀ f ∈ Submodule.span ℂ K, ∀ (h : f ∈ Sm E a) (Y : Lie E a),
      (lie E a Y ⟨f, h⟩).1 ∈ Submodule.span ℂ K := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      intro h Y
      obtain ⟨fs, h1, h2⟩ := hder f hf
      have e : (lie E a Y ⟨f, h⟩).1 = ∑ p, (lieCoord E a p.2 Y) • fs p := by
        funext g
        rw [CuspRep.lie_apply, lieD, (h2 g).fderiv]
        simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
          smul_eq_mul, mul_comm]
      rw [e]
      exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (h1 p))
    | zero =>
      intro h Y
      have : (⟨0, h⟩ : Sm E a) = 0 := rfl
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | add f f' hf hf' ihf ihf' =>
      intro h Y
      have : (⟨f + f', h⟩ : Sm E a) = ⟨f, hspan hf⟩ + ⟨f', hspan hf'⟩ := rfl
      rw [this, map_add]
      exact Submodule.add_mem _ (ihf _ Y) (ihf' _ Y)
    | smul c f hf ihf =>
      intro h Y
      have : (⟨c • f, h⟩ : Sm E a) = c • ⟨f, hspan hf⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem _ c (ihf _ Y)
  have hword : ∀ (l : List (Lie E a)) (ψ : Sm E a), ψ.1 ∈ Submodule.span ℂ K →
      (GlobalTheory.GLFin.word l ψ).1 ∈ Submodule.span ℂ K := by
    intro l
    induction l with
    | nil => intro ψ h; rwa [word_nil]
    | cons Y l ih => intro ψ h; rw [word_cons]; exact hlie _ (ih ψ h) _ Y
  have hgood : Submodule.span ℂ K ≤ mspanR π ⊓ bccSub E a := Submodule.span_le.2 (by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ []
    rw [word_nil] at h1 h2
    exact ⟨mspanR_kerOp h1 ν k γ hk, isBCC_kerOp ν k γ hk φ h2⟩)
  have hmem : kerOp ν k γ φ.1 ∈ K := ⟨X, _, ν, inferInstance, k, γ, φ, hk, hφ, rfl⟩
  exact ⟨⟨_, hSm _ hmem⟩, mem_dSub.2 fun l => hgood (hword l _ (Submodule.subset_span hmem)), rfl⟩

theorem mspanR_le (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    mspanR π ≤ (dSub π).map (Sm E a).subtype := by
  refine sInf_le ⟨fun φ hφ => ⟨φ, mem_dSub_of_mem hB hπ hφ, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩ h
    exact ⟨rt E a h φ, rt_mem_dSub hφ h, rfl⟩
  · rintro _ ⟨φ, hφ, rfl⟩ X _ ν _ k γ hk
    obtain ⟨ψ, h1, h2⟩ := kerOp_mem_dSub hφ ν k γ hk
    exact ⟨ψ, h1, h2⟩

theorem mspanR_words (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  intro F hF
  obtain ⟨φ, hφ, rfl⟩ := mspanR_le hB hπ hF
  exact ⟨φ, rfl, mem_dSub.1 hφ⟩

theorem mspanR_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    GlobalTheory.Published.CuspFormsBoundedGL → ∀ π : CuspSub E a, π.IsUnitary → ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      (∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  intro E _ _ _ a hB π hπ F hF
  obtain ⟨φ, rfl, h⟩ := mspanR_words hB hπ F hF
  have h0 := (h []).2
  rw [word_nil] at h0
  exact ⟨φ, rfl, fun l => (h l).1, h0.cusp, h0.bdd⟩

end GlobalTheory.JSW
