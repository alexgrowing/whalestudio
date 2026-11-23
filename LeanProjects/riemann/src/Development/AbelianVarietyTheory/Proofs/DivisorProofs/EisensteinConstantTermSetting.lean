import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransversalForIsotropicColumnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermRationalUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalHaarIntegralConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirichletSeriesIntegralHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesFunctionalBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinLineSumUnipotentInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermFormulaStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

open GlobalTheory.EisCT in

theorem GlobalTheory.EisCT.constTerm : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c → ∃ mid : ℂ → GAd σ J → ℂ, (∀ g, DifferentiableOn ℂ (mid · g) {s : ℂ | ((n : ℝ) - 1) / 2 - 1 < s.re}) ∧ (∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g, ∫ u in 𝓕, Eis s (u.1 * g) ∂μ =
        (h g : ℂ) ^ (s + (((n : ℂ) - 1) / 2)) + mid s g + c s * (h g : ℂ) ^ (-s + (((n : ℂ) - 1) / 2))) := by
  intro hpr F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_transversal_for_isotropic_column F E σ n J (col0 X)
  have hpos : ∀ g, 0 < h g := by
    intro g
    obtain ⟨p, l, hp, k, hk, rfl⟩ := hS.2.2.2.2.2.2.1 g
    rw [hS.2.2.2.2.2.2.2 p l hp k hk]
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact_mod_cast pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1)
  have hcont := GlobalTheory.T.eisenstein_setting_height_continuous F E σ n J r X Y L a h hS
  have hmeas : ∀ (g : GAd σ J) (t : midSet σ J (col0 X) T),
      Measurable (fun u : unipRad σ J (col0 X) => h (t.1.1 * (u.1 * g))) := fun g t =>
    (hcont.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const))).measurable
  have hG : ∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 → ∀ g,
      (∀ z : ℂ, (n : ℝ) - 2 < z.re → Integrable (fun u : unipRad σ J (col0 X) =>
        ∑' t : midSet σ J (col0 X) T, (h (t.1.1 * (u.1 * g)) : ℂ) ^ z) (μ.restrict 𝓕)) ∧
      DifferentiableOn ℂ (fun z : ℂ => ∫ u, ∑' t : midSet σ J (col0 X) T, (h (t.1.1 * (u.1 * g)) : ℂ) ^ z
        ∂(μ.restrict 𝓕)) {z | (n : ℝ) - 2 < z.re} :=
    fun μ 𝓕 hμ h𝓕 h1 g => GlobalTheory.T.dirichlet_series_integral_holomorphic (μ.restrict 𝓕)
      (fun (t : midSet σ J (col0 X) T) (u : unipRad σ J (col0 X)) => h (t.1.1 * (u.1 * g))) ((n : ℝ) - 2)
      (hmeas g) (fun _ _ => hpos _) (fun s hs => GlobalTheory.T.unipotent_radical_haar_integral_constant hpr F E σ n J r X Y L a h hS T hT μ 𝓕 hμ h𝓕 h1 s hs g)
  have hre : ∀ s : ℂ, ((n : ℝ) - 1) / 2 - 1 < s.re → (n : ℝ) - 2 < (s + ((n : ℂ) - 1) / 2).re := by
    intro s hs
    have e : ((n : ℂ) - 1) / 2 = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.add_re, Complex.ofReal_re]
    linarith
  by_cases hex : ∃ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ ∧ μ 𝓕 = 1
  swap
  · exact ⟨fun _ _ => 0, fun g => differentiableOn_const 0, fun μ 𝓕 hμ h𝓕 h1 => (hex ⟨μ, 𝓕, hμ, h𝓕, h1⟩).elim⟩
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h1₀⟩ := hex
  refine ⟨fun s g => ∫ u in 𝓕₀, midSum σ J (col0 X) T h s (u.1 * g) ∂μ₀, fun g => ?_, ?_⟩
  · exact (hG μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀ g).2.comp (differentiable_id.add_const _).differentiableOn fun s hs => hre s hs
  · intro μ 𝓕 hμ h𝓕 h1 s hs g
    have hsplit : ∀ u : unipRad σ J (col0 X), Eis s (u.1 * g) = lineSum σ J (col0 X) T h s (u.1 * g) +
        midSum σ J (col0 X) T h s (u.1 * g) + bigSum σ J (col0 X) T h s (u.1 * g) := fun u =>
      GlobalTheory.T.eisenstein_eq_lineSum_add_midSum_add_bigSum F E σ n J r X Y L a h Eis hS hP.1 T hT s hs (u.1 * g)
    have hline : ∀ u : unipRad σ J (col0 X), lineSum σ J (col0 X) T h s (u.1 * g) = fs σ J h s g := fun u =>
      GlobalTheory.T.eisenstein_line_sum_unipotent_invariant F E σ n J r X Y L a h hS T hT u.1 u.2 s g
    have hmidI : IntegrableOn (fun u : unipRad σ J (col0 X) => midSum σ J (col0 X) T h s (u.1 * g)) 𝓕 μ :=
      (hG μ 𝓕 hμ h𝓕 h1 g).1 _ (hre s (by linarith))
    obtain ⟨hbigI, hbig⟩ := GlobalTheory.T.eisenstein_constant_term_formula F E σ n J r X Y L a h Eis c hS hP T hT μ 𝓕 hμ h𝓕 h1 s hs g
    have hfin : μ 𝓕 ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
    have hlineI : IntegrableOn (fun u : unipRad σ J (col0 X) => lineSum σ J (col0 X) T h s (u.1 * g)) 𝓕 μ := by
      have : (fun u : unipRad σ J (col0 X) => lineSum σ J (col0 X) T h s (u.1 * g)) = fun _ => fs σ J h s g :=
        funext hline
      rw [this]
      exact integrableOn_const hfin
    have hmideq : ∫ u in 𝓕, midSum σ J (col0 X) T h s (u.1 * g) ∂μ =
        ∫ u in 𝓕₀, midSum σ J (col0 X) T h s (u.1 * g) ∂μ₀ :=
      GlobalTheory.T.unipotent_invariant_function_expansion F E σ n J r X Y L a h hS (fun u => midSum σ J (col0 X) T h s (u.1 * g)) (fun ν u => by
        show midSum σ J (col0 X) T h s (((ν : unipRad σ J (col0 X)) * u).1 * g) = _
        rw [Subgroup.coe_mul, mul_assoc]
        exact GlobalTheory.T.eisenstein_constant_term_rational_unipotent F E σ n J r X Y L a h hS T hT _ (Subgroup.mem_subgroupOf.1 ν.2) ν.1.2 s _)
        μ 𝓕 hμ h𝓕 h1 μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀
    calc ∫ u in 𝓕, Eis s (u.1 * g) ∂μ
        = ∫ u in 𝓕, (lineSum σ J (col0 X) T h s (u.1 * g) + midSum σ J (col0 X) T h s (u.1 * g) +
            bigSum σ J (col0 X) T h s (u.1 * g)) ∂μ := integral_congr_ae (ae_of_all _ hsplit)
      _ = (∫ u in 𝓕, lineSum σ J (col0 X) T h s (u.1 * g) ∂μ) + (∫ u in 𝓕, midSum σ J (col0 X) T h s (u.1 * g) ∂μ) +
            ∫ u in 𝓕, bigSum σ J (col0 X) T h s (u.1 * g) ∂μ := by
        rw [integral_add _ hbigI, integral_add hlineI hmidI]
        exact hlineI.add hmidI
      _ = _ := by
        rw [hmideq, hbig, integral_congr_ae (ae_of_all _ hline), setIntegral_const]
        simp [fs, Measure.real, h1]

end
