import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSm_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') : IsSm σ J (f + f') :=
  fun k γ hγ g => (h k γ hγ g).add (h' k γ hγ g)

theorem isSm_smul (a : ℂ) {f : GAd σ J → ℂ} (h : IsSm σ J f) : IsSm σ J (a • f) :=
  fun k γ hγ g => (h k γ hγ g).const_smul a

theorem differentiable_of_isSm {f : GAd σ J → ℂ} (h : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (g : GAd σ J) : Differentiable ℝ fun t : ℝ => f (g * γ t) := by
  have h1 := h 1 (fun _ => γ) (fun _ => hγ) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h1.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem lineDer_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) : lineDer γ (f + f') = lineDer γ f + lineDer γ f' := by
  funext g
  exact deriv_fun_add (differentiable_of_isSm h hγ g 0) (differentiable_of_isSm h' hγ g 0)

omit [NumberField E] in
theorem lineDer_smul (a : ℂ) (f : GAd σ J → ℂ) (γ : ℝ → GAd σ J) : lineDer γ (a • f) = a • lineDer γ f := by
  funext g
  simp only [lineDer, Pi.smul_apply, smul_eq_mul, deriv_const_mul_field']

theorem isSm_lineDer {f : GAd σ J → ℂ} (hf : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSm σ J (lineDer γ f) := by
  intro k γs h g
  have h1 := hf (k + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) γs γ)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hγ
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      f (g * (List.ofFn fun i => γs i (t i)).prod * γ s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem isSm_foldr {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f : GAd σ J → ℂ}
    (hf : IsSm σ J f) : IsSm σ J (l.foldr lineDer f) := by
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    exact isSm_lineDer (ih fun δ hδ => hl δ (by simp [hδ])) (hl γ (by simp))

theorem foldr_add {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f f' : GAd σ J → ℂ}
    (hf : IsSm σ J f) (hf' : IsSm σ J f') : l.foldr lineDer (f + f') = l.foldr lineDer f + l.foldr lineDer f' := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    have hl' : ∀ δ ∈ l, IsRealLine σ J δ := fun δ hδ => hl δ (by simp [hδ])
    simp only [List.foldr_cons]
    rw [ih hl', lineDer_add (isSm_foldr hl' hf) (isSm_foldr hl' hf') (hl γ (by simp))]

omit [NumberField E] in
theorem foldr_smul (l : List (ℝ → GAd σ J)) (a : ℂ) (f : GAd σ J → ℂ) :
    l.foldr lineDer (a • f) = a • l.foldr lineDer f := by
  induction l with
  | nil => rfl
  | cons γ l ih => simp only [List.foldr_cons, ih, lineDer_smul]

theorem dop_add {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ)
    {f f' : GAd σ J → ℂ} (hf : IsSm σ J f) (hf' : IsSm σ J f') : dop z (f + f') = dop z f + dop z f' := by
  funext g
  simp only [dop, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [foldr_add (hz l hl) hf hf', Pi.add_apply, mul_add]

omit [NumberField E] in
theorem dop_smul (z : List (ℝ → GAd σ J) →₀ ℂ) (a : ℂ) (f : GAd σ J → ℂ) : dop z (a • f) = a • dop z f := by
  funext g
  simp only [dop, Finsupp.sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, foldr_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isAutOn_add_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (H K : Subgroup (GAd σ J)) (φ ψ : GAd σ J → ℂ) (a : ℂ), IsAutOn σ J H K φ → IsAutOn σ J H K ψ →
    IsAutOn σ J H K (φ + ψ) ∧ IsAutOn σ J H K (a • φ) := by
  intro F E _ _ _ _ _ σ _ n J _ H K φ ψ a h h'
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont, isSm_add h.smooth h'.smooth, ?_, h.kfin.add h'.kfin, ?_⟩,
    ⟨fun γ hγ g => ?_, ?_, h.cont.const_smul a, isSm_smul a h.smooth, ?_, ?_, ?_⟩⟩
  · simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    obtain ⟨U', hU', hk'⟩ := h'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k h1 h2 g => by simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    refine ⟨max N N', fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    obtain ⟨C', hC'⟩ := hN' l hl
    refine ⟨|C| + |C'|, fun g => ?_⟩
    have h1 : (1 : ℝ) ≤ height σ J g := by exact_mod_cast one_le_height σ J g
    have h0 : (0 : ℝ) ≤ height σ J g := zero_le_one.trans h1
    rw [foldr_add hl h.smooth h'.smooth, Pi.add_apply, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hC g).trans ?_) ((hC' g).trans ?_))
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_left _ _)) (pow_nonneg h0 _) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_right _ _)) (pow_nonneg h0 _) (abs_nonneg _)
  · haveI := h.zfin
    haveI := h'.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ} ⊔
      Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z ψ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    rw [dop_add hz.1 h.smooth h'.smooth]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · simp only [Pi.smul_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    refine ⟨‖a‖ * C, fun g => ?_⟩
    rw [foldr_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)
  · obtain ⟨W, hW, e⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h.kfin
    exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => W.smul_mem a (e k hk)⟩
  · haveI := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    rw [dop_smul]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz, rfl⟩)

end GlobalTheory.UAut

end
