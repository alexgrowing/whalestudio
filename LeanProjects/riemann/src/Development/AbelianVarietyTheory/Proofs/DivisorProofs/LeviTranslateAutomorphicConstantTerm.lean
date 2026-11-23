import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.LeviShift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section General

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {H K : Subgroup (GAd σ J)}

omit [NumberField E] in
theorem foldr_left (g₀ : GAd σ J) (f : GAd σ J → ℂ) (l : List (ℝ → GAd σ J)) :
    l.foldr lineDer (fun x => f (g₀ * x)) = fun x => l.foldr lineDer f (g₀ * x) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    simp only [List.foldr_cons, ih]
    funext g
    simp only [lineDer, mul_assoc]

theorem isAutOn_left {f : GAd σ J → ℂ} (h : IsAutOn σ J H K f) (g₀ : GAd σ J) (hg : ∀ γ ∈ H, g₀ * γ * g₀⁻¹ ∈ H) :
    IsAutOn σ J H K fun x => f (g₀ * x) := by
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_const.mul continuous_id), fun k γ hγ g => ?_, ?_, ?_, ?_⟩
  · have := h.left _ (hg γ hγ) (g₀ * g)
    simpa [mul_assoc] using this
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simpa only [mul_assoc] using hk k h1 h2 (g₀ * g)⟩
  · simpa only [mul_assoc] using h.smooth k γ hγ (g₀ * g)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    refine ⟨|C| * (height σ J g₀ : ℝ) ^ N, fun g => ?_⟩
    rw [foldr_left, mul_assoc, ← mul_pow]
    refine (hC _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ _)
      (pow_nonneg (NNReal.coe_nonneg _) _) (abs_nonneg _))
    exact_mod_cast height_mul_le σ J g₀ g
  · obtain ⟨W, hW, e⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h.kfin
    exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W.map (LinearMap.funLeft ℂ ℂ (g₀ * ·)), inferInstance,
      fun k hk => ⟨_, e k hk, funext fun x => by simp [LinearMap.funLeft_apply, mul_assoc]⟩⟩
  · haveI := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ {f' | ∃ z, IsCentral σ J z ∧ f' = dop z f}).map
      (LinearMap.funLeft ℂ ℂ (g₀ * ·))) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, funext fun x => ?_⟩
    simp only [LinearMap.funLeft_apply, dop, foldr_left]

theorem isAutOn_add {φ ψ : GAd σ J → ℂ} (h : IsAutOn σ J H K φ) (h' : IsAutOn σ J H K ψ) : IsAutOn σ J H K (φ + ψ) := by
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont, isSm_add h.smooth h'.smooth, ?_, h.kfin.add h'.kfin, ?_⟩
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

theorem isAutOn_smul (a : ℂ) {φ : GAd σ J → ℂ} (h : IsAutOn σ J H K φ) : IsAutOn σ J H K (a • φ) := by
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.const_smul a, isSm_smul a h.smooth, ?_, ?_, ?_⟩
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

end General

theorem conj_mem_unip {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {P : Plane E n n₁} {t : (AE F E)ˣ} {m : UA σ Y.J}
    (hm : IsLevi (W₁ := Y₁) P t 1 m) {u : UA σ Y.J} (hu : u ∈ unip σ Y P) : m * u * m⁻¹ ∈ unip σ Y P := by
  obtain ⟨h1, -, h2⟩ := hm
  have hmul : ∀ a b : UA σ Y.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have hone : mat (1 : UA σ Y.J) = 1 := rfl
  have h2' : mat m * incM F P.ι = incM F P.ι := h2.trans (Matrix.mul_one _)
  have hinv : mat m⁻¹ * mat m = 1 := by rw [← hmul, inv_mul_cancel, hone]
  have h3 : mat m⁻¹ * incM F P.ι = incM F P.ι := by
    conv_lhs => rw [← h2', ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have h4 : mat m⁻¹ *ᵥ incV F P.x = (t⁻¹).1 • incV F P.x := by
    have := congrArg (fun v => (t⁻¹).1 • (mat m⁻¹ *ᵥ v)) h1
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm
  have : unip σ Y P ≤ (unip σ Y P).comap (MulAut.conj m).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun v hv => Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · change mat (m * v * m⁻¹) *ᵥ _ = _
      rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_smul, hv.1, Matrix.mulVec_smul, h1,
        smul_smul, Units.inv_mul, one_smul]
    · obtain ⟨a, ha⟩ := hv.2 z
      refine ⟨a * t.1, ?_⟩
      change mat (m * v * m⁻¹) *ᵥ _ = _
      rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, h3, ha, Matrix.mulVec_add,
        Matrix.mulVec_mulVec z, h2', Matrix.mulVec_smul, h1, smul_smul]
  exact this hu

theorem isAutOn_levi_comb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁) (c : E) (hc : c ≠ 0)
    (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) P t 1 m →
    ∀ (φ : UA σ Y.J → ℂ) (a b : ℂ) (K : Subgroup (GAd σ (c • Y.J.map σ))),
      IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => φ ((toGAd hσ Y.J hc).symm x)) →
      IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => a * φ (m * (toGAd hσ Y.J hc).symm x) + b * φ ((toGAd hσ Y.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ n n₁ Y Y₁ P c hc t m hm φ a b K h
  have h1 := isAutOn_left h (toGAd hσ Y.J hc m) (by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨m * u * m⁻¹, conj_mem_unip hm hu, by simp⟩)
  have h2 := isAutOn_add (isAutOn_smul a h1) (isAutOn_smul b h)
  convert h2 using 1
  funext x
  simp

end GlobalTheory.ThK.LeviShift

end
