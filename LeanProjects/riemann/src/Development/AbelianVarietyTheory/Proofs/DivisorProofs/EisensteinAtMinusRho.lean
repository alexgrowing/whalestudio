import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermSettingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyUniformModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRhoOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermSettingAltBis

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.EisRes.eisCore_of_kazhdanPatterson (hK : GlobalTheory.ThK.KP) : EisCore := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hcm, hun, hJ, hn, hW, hA, hI⟩ := hS
  obtain ⟨Eis, c, p1, p2, p3, p4, p5⟩ := hK.eisensteinIsotropicLine F E σ hcm hun n J hJ r X Y hW (col0 X) (col0 Y)
    rfl rfl L a hA h hI.1 hI.2
  have hP : EisensteinHyp σ J (col0 X) (col0 Y) h Eis c := ⟨p1, p2, p3, p4, p5⟩
  have hS : HidaSetting σ J X Y L a h := ⟨hcm, hun, hJ, hn, hW, hA, hI⟩
  obtain ⟨mid, hmid, hct⟩ := GlobalTheory.T.eisenstein_constant_term_setting hK.eisensteinIsotropicLine F E σ n J r X Y L a h Eis c hS hP
  obtain ⟨u, U₀, U₁, Hol, C, N, ⟨hU₀, hu, hu0, hcu⟩, hU₁, hHol, hHd, hHb, hHρ⟩ :=
    GlobalTheory.T.eisenstein_constant_term_setting_alt hK.eisensteinResidueLine F E σ n J r X Y L a h Eis c hS hP mid hmid hct
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hpos : 0 < ‖u ρ‖ := norm_pos_iff.2 hu0
  have hev : ∀ᶠ s in 𝓝 (-ρ), (s ≠ -ρ → c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g) ∧ -s ∈ U₀ ∧ -s ∈ U₁ ∧
      ‖u ρ‖ / 2 < ‖u (-s)‖ := by
    have t : Tendsto (fun s : ℂ => -s) (𝓝 (-ρ)) (𝓝 ρ) := by simpa using (continuous_neg.tendsto (-ρ))
    have hucont : ContinuousAt u ρ := (hu.differentiableAt hU₀).continuousAt
    refine ((eventually_nhdsWithin_iff.1 (p5 (-ρ))).mono fun s hs hne => hs hne).and
      ((t.eventually hU₀).and ((t.eventually hU₁).and ?_))
    have : Tendsto (fun s : ℂ => ‖u (-s)‖) (𝓝 (-ρ)) (𝓝 ‖u ρ‖) :=
      (continuous_norm.tendsto _).comp (hucont.tendsto.comp t)
    exact this.eventually_const_lt (by linarith)
  obtain ⟨V, hV, hVs⟩ := hev.exists_mem
  let Eis' : ℂ → GAd σ J → ℂ := fun s g => if s = -ρ then 1 else Eis s g
  have hform : ∀ s ∈ V, ∀ g, Eis' s g = Hol (-s) g / u (-s) := by
    intro s hs g
    obtain ⟨h1, h2, h3, h4⟩ := hVs s hs
    by_cases e : s = -ρ
    · subst e
      simp [Eis', hHρ, div_self hu0]
    · have hne : -s ≠ ρ := fun h' => e (by rw [← h', neg_neg])
      have hu' : u (-s) ≠ 0 := fun h0 => by rw [h0, norm_zero] at h4; linarith
      have hd : -s - ρ ≠ 0 := sub_ne_zero.2 hne
      obtain ⟨hc1, hc2⟩ := h1 e
      have hc' : c s * (u (-s) / (-s - ρ)) = 1 := by rw [← hcu (-s) h2 hne]; exact hc1
      simp only [Eis', if_neg e]
      rw [hc2 g, hHol (-s) h3 hne g]
      field_simp at hc' ⊢
      linear_combination Eis (-s) g * hc'
  have hneg : ∃ U ∈ 𝓝 (-ρ), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis' · g) U ∧
      (∀ s ∈ U, ‖Eis' s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧ Eis' (-ρ) g = 1 := by
    refine ⟨V, hV, 2 * C / ‖u ρ‖, N, fun g => ⟨?_, ?_, by simp [Eis']⟩⟩
    · have hd : DifferentiableOn ℂ (fun s => Hol (-s) g / u (-s)) V := by
        refine DifferentiableOn.div ((hHd g).comp differentiable_neg.differentiableOn fun s hs => (hVs s hs).2.2.1)
          (hu.comp differentiable_neg.differentiableOn fun s hs => (hVs s hs).2.1) fun s hs => ?_
        have := (hVs s hs).2.2.2
        intro h0; rw [h0, norm_zero] at this; linarith
      exact hd.congr fun s hs => hform s hs g
    · intro s hs
      rw [hform s hs g, norm_div]
      have h1 := hHb (-s) (hVs s hs).2.2.1 g
      have h2 := (hVs s hs).2.2.2
      have h0 : 0 ≤ C * (height σ J g : ℝ) ^ N := (norm_nonneg _).trans h1
      calc ‖Hol (-s) g‖ / ‖u (-s)‖ ≤ C * (height σ J g : ℝ) ^ N / (‖u ρ‖ / 2) :=
            div_le_div₀ h0 h1 (by linarith) h2.le
        _ = 2 * C / ‖u ρ‖ * (height σ J g : ℝ) ^ N := by field_simp
  refine ⟨Eis', ?_, ?_, hneg⟩
  · intro T hT s hs g
    have hne : s ≠ -ρ := by
      rintro rfl
      have e : (-ρ).re = -(((n : ℝ) - 1) / 2) := by simp [hρ]
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
      rw [e] at hs
      linarith
    simpa [Eis', hne] using p1 T hT s hs g
  · intro s₀
    by_cases h0 : s₀ = -ρ
    · subst h0
      obtain ⟨V', hV', C', N', hall⟩ := hneg
      exact ⟨0, V', Eis', C', N', hV', fun s _ _ g => by simp, fun g => (hall g).1, fun s hs g => (hall g).2.1 s hs⟩
    · obtain ⟨k, U, H, hU, hH, hsm, hhol⟩ := p4 s₀
      obtain ⟨V', hV', C', N', hb⟩ := GlobalTheory.WeakHolFamily.locally_uniform_moderate_growth F E σ n J H s₀ U hU hsm hhol
      refine ⟨k, U ∩ V' ∩ {-ρ}ᶜ, H, C', N', Filter.inter_mem (Filter.inter_mem hU hV')
        (isOpen_compl_singleton.mem_nhds h0), fun s hs hs0 g => ?_, fun g => ?_, fun s hs g => hb s hs.1.2 g⟩
      · have e : s ≠ -ρ := hs.2
        simp only [Eis', if_neg e]
        exact hH s hs.1.1 hs0 g
      · exact (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono fun s hs => hs.1.1

theorem GlobalTheory.ConeSmall.eisAtMinusRho : GlobalTheory.ThK.KP → GlobalTheory.ConeSmall.EisAtMinusRho := fun hK =>
  GlobalTheory.EisReduce.eisAtMinusRho_of_core (GlobalTheory.EisRes.eisCore_of_kazhdanPatterson hK)

end
