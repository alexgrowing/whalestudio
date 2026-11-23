import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDerivativeBoundSettingStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT.LimCT

theorem tendsto_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 (((n : ℂ) - 1) / 2) → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H s g = (s - (((n : ℂ) - 1) / 2)) ^ k * Eis s g) →
      ∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 → ∀ g,
        IntegrableOn (fun u : unipRad σ J (col0 X) => H (((n : ℂ) - 1) / 2) (u.1 * g)) 𝓕 μ ∧
        Tendsto (fun s => ∫ u in 𝓕, H s (u.1 * g) ∂μ) (𝓝[≠] (((n : ℂ) - 1) / 2)) (𝓝 (∫ u in 𝓕, H (((n : ℂ) - 1) / 2) (u.1 * g) ∂μ)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k U H hU hHd hHE μ 𝓕 hμ h𝓕 h1 g
  obtain ⟨V, hV, C, N, hbd⟩ := GlobalTheory.T.eisenstein_derivative_bound_setting F E σ n J r X Y L a h Eis c hS hP k U H hU hHd hHE
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  obtain ⟨hCM, -, hJ, -, hW, -, -⟩ := hS
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (col0 X) := by
    have e : col0 X = X.submatrix id (Fin.castLE (show 1 ≤ r + 1 by omega)) := by
      ext i j
      rw [Subsingleton.elim j 0]
      rfl
    rw [e]
    exact GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ _
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((NNReal.continuous_coe.comp ((GlobalTheory.AdelicU.continuous_height_GAd σ J).comp continuous_subtype_val)) :
      Continuous fun u : unipRad σ J (col0 X) => (height σ J u.1 : ℝ)).continuousOn
  obtain ⟨-, -, -, hcont, -⟩ := hP
  obtain ⟨k₀, U₀, H₀, hU₀, hH₀E, hH₀S, -⟩ := hcont ρ

  have hWn : U ∩ U₀ ∩ V ∈ 𝓝 ρ := inter_mem (inter_mem hU hU₀) hV
  have hEis : ∀ s ∈ U₀, s ≠ ρ → ∀ g', Eis s g' = H₀ s g' / (s - ρ) ^ k₀ := fun s hs hne g' => by
    rw [hH₀E s hs hne g', mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 hne))]
  have hHs : ∀ s ∈ U ∩ U₀ ∩ V, s ≠ ρ → ∀ g', H s g' = (s - ρ) ^ k * (H₀ s g' / (s - ρ) ^ k₀) := fun s hs hne g' => by
    rw [hHE s hs.1.1 hne g', hEis s hs.1.2 hne g']
  have hcontS : ∀ s ∈ U ∩ U₀ ∩ V, s ≠ ρ → Continuous (H s) := fun s hs hne => by
    have : H s = fun g' => (s - ρ) ^ k * (H₀ s g' / (s - ρ) ^ k₀) := funext (hHs s hs hne)
    rw [this]
    exact continuous_const.mul ((hH₀S s hs.1.2).cont.div_const _)
  have hlim : ∀ g', Tendsto (fun s => H s g') (𝓝[≠] ρ) (𝓝 (H ρ g')) := fun g' =>
    (((hHd g').continuousOn.continuousAt hU).tendsto).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] ρ, s ∈ U ∩ U₀ ∩ V ∧ s ≠ ρ :=
    (eventually_nhdsWithin_of_eventually_nhds hWn).and self_mem_nhdsWithin
  have hinvS : ∀ s ∈ U ∩ U₀ ∩ V, s ≠ ρ → ∀ γ ∈ ratPts σ J, ∀ g', H s (γ * g') = H s g' :=
    fun s hs hne γ hγ g' => by rw [hHs s hs hne, hHs s hs hne, (hH₀S s hs.1.2).left γ hγ]
  have hinv : ∀ s ∈ U ∩ U₀ ∩ V, ∀ γ ∈ ratPts σ J, ∀ g', H s (γ * g') = H s g' := by
    intro s hs γ hγ g'
    by_cases hne : s = ρ
    · subst hne
      exact tendsto_nhds_unique ((hlim (γ * g')).congr' (hev.mono fun t ht => hinvS t ht.1 ht.2 γ hγ g')) (hlim g')
    · exact hinvS s hs hne γ hγ g'

  have hC0 : 0 ≤ C := by
    have h1' := (norm_nonneg _).trans (hbd ρ (mem_of_mem_nhds hV) g)
    have hp : 0 < (height σ J g : ℝ) ^ N :=
      pow_pos (lt_of_lt_of_le one_pos (by exact_mod_cast GlobalTheory.AdelicU.one_le_height σ J g)) N
    exact le_of_mul_le_mul_right (by simpa using h1') hp
  have hM0 : 0 ≤ M := by
    obtain ⟨γ, -, hγK⟩ := hcov 1
    exact (norm_nonneg _).trans (hM _ hγK)
  set B : ℝ := C * (M * (height σ J g : ℝ)) ^ N with hB
  have hbound : ∀ s ∈ U ∩ U₀ ∩ V, ∀ u : unipRad σ J (col0 X), ‖H s (u.1 * g)‖ ≤ B := by
    intro s hs u
    obtain ⟨γ, hγ, hγK⟩ := hcov u
    have e1 : H s (u.1 * g) = H s ((γ * u).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hinv s hs _ (Subgroup.mem_subgroupOf.1 hγ)]
    rw [e1]
    refine (hbd s hs.2 _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    refine pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ N
    have h2 : (height σ J ((γ * u).1 * g) : ℝ) ≤ (height σ J (γ * u).1 : ℝ) * height σ J g := by
      exact_mod_cast GlobalTheory.AdelicU.height_mul_le σ J _ _
    have h3 : (height σ J (γ * u).1 : ℝ) ≤ M := by
      have := hM _ hγK
      simp only [Function.comp_apply] at this
      rwa [Real.norm_of_nonneg (NNReal.coe_nonneg _)] at this
    exact h2.trans (mul_le_mul_of_nonneg_right h3 (NNReal.coe_nonneg _))

  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hmeasS : ∀ s ∈ U ∩ U₀ ∩ V, s ≠ ρ →
      AEStronglyMeasurable (fun u : unipRad σ J (col0 X) => H s (u.1 * g)) (μ.restrict 𝓕) := fun s hs hne =>
    ((hcontS s hs hne).comp ((continuous_subtype_val).mul continuous_const)).aestronglyMeasurable
  have hmeasρ : AEStronglyMeasurable (fun u : unipRad σ J (col0 X) => H ρ (u.1 * g)) (μ.restrict 𝓕) := by
    classical
    let f : ℂ → unipRad σ J (col0 X) → ℂ := fun s => if s ∈ U ∩ U₀ ∩ V ∧ s ≠ ρ then fun u => H s (u.1 * g) else 0
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] ρ) (f := f) (fun s => ?_) (.of_forall fun u => ?_)
    · by_cases hs : s ∈ U ∩ U₀ ∩ V ∧ s ≠ ρ
      · simp only [f, if_pos hs]; exact hmeasS s hs.1 hs.2
      · simp only [f, if_neg hs]; exact aestronglyMeasurable_const
    · refine (hlim (u.1 * g)).congr' (hev.mono fun t ht => ?_)
      simp only [f, if_pos ht]
  refine ⟨(integrable_const B).mono' hmeasρ (.of_forall fun u => hbound ρ (mem_of_mem_nhds hWn) u), ?_⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    (hev.mono fun s hs => hmeasS s hs.1 hs.2) (hev.mono fun s hs => .of_forall fun u => hbound s hs.1 u)
    (integrable_const B) (.of_forall fun u => hlim (u.1 * g))

end GlobalTheory.EisCT.LimCT
