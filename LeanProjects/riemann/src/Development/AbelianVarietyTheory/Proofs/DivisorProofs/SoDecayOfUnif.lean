import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) : (1 : ℝ) ≤ (ht h : ℝ) := by
  unfold ht
  exact_mod_cast one_le_heightGL F h.1

theorem soDecay_of_unif : GlobalTheory.FunPr.Hypotheses₂ → SoDecayUnif → SoDecay := by
  intro _ hU F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair Φ hΦ
  have hS := hPair.weil.isUSplitting
  obtain ⟨l, -, hlt⟩ := GlobalTheory.T.exists_admissibleForm_adelicThetaSum F (Fin n × Fin d)
  have hsch : M.So B.ψ B.τ₁ ≤ schA F (Fin n × Fin d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    have h3 := (h2.and hPair.good.std).mono fun w hw => hw.1.trans hw.2
    exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩
  have hlin : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ g h, theta om Ψ g h = l (om (g, h) Ψ) :=
    fun Ψ hΨ g h => (hlt _ (hS.pres _ _ hΨ)).symm
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, h1, h2, h3, rfl⟩ := hx
    have hstd := (h2.and hPair.good.std).mono fun w hw => hw.1.trans hw.2
    have hφ : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
      ⟨isLocallyConstant_finprod_evalV φ h1 hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 hstd⟩
    have hall : ∀ f' : SInf F (Fin n × Fin d),
        pureA F f' (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈
          M.So B.ψ B.τ₁ :=
      fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩
    intro N
    obtain ⟨C, k, hC⟩ := hU F E σ B n d X W M χX χW om r s r' s' hPair _ hφ hall N
    exact ⟨C * semK (Fin n × Fin d) k f, k, fun g h => hC f g h⟩
  | zero =>
    intro N
    refine ⟨0, 0, fun g h => ?_⟩
    simp [theta, thetaSum]
  | add x y hx hy ihx ihy =>
    intro N
    obtain ⟨C1, k1, h1⟩ := ihx N
    obtain ⟨C2, k2, h2⟩ := ihy N
    refine ⟨max C1 0 + max C2 0, max k1 k2, fun g h => ?_⟩
    have e : theta om (x + y) g h = theta om x g h + theta om y g h := by
      rw [hlin _ (add_mem (hsch hx) (hsch hy)), hlin _ (hsch hx), hlin _ (hsch hy), map_add, map_add]
    have hh := one_le_ht h
    have hh0 : (0 : ℝ) ≤ (ht h : ℝ) := zero_le_one.trans hh
    have q0 : (0 : ℝ) ≤ (qht g : ℝ) ^ N := pow_nonneg (NNReal.coe_nonneg _) N
    have b1 : C1 * (ht h : ℝ) ^ k1 ≤ max C1 0 * (ht h : ℝ) ^ max k1 k2 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hh0 _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (le_max_left _ _)) (le_max_right _ _))
    have b2 : C2 * (ht h : ℝ) ^ k2 ≤ max C2 0 * (ht h : ℝ) ^ max k1 k2 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hh0 _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (le_max_right _ _)) (le_max_right _ _))
    calc ‖theta om (x + y) g h‖ * (qht g : ℝ) ^ N
        ≤ ‖theta om x g h‖ * (qht g : ℝ) ^ N + ‖theta om y g h‖ * (qht g : ℝ) ^ N := by
          rw [e, ← add_mul]
          exact mul_le_mul_of_nonneg_right (norm_add_le _ _) q0
      _ ≤ C1 * (ht h : ℝ) ^ k1 + C2 * (ht h : ℝ) ^ k2 := add_le_add (h1 g h) (h2 g h)
      _ ≤ max C1 0 * (ht h : ℝ) ^ max k1 k2 + max C2 0 * (ht h : ℝ) ^ max k1 k2 := add_le_add b1 b2
      _ = (max C1 0 + max C2 0) * (ht h : ℝ) ^ max k1 k2 := by ring
  | smul c x hx ihx =>
    intro N
    obtain ⟨C, k, h1⟩ := ihx N
    refine ⟨‖c‖ * C, k, fun g h => ?_⟩
    have e : theta om (c • x) g h = c * theta om x g h := by
      rw [hlin _ (Submodule.smul_mem _ c (hsch hx)), hlin _ (hsch hx), map_smul, map_smul, smul_eq_mul]
    rw [e, norm_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 g h) (norm_nonneg c)

end GlobalTheory.ThKSoSpan
