import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.VMove

set_option maxHeartbeats 4000000 in

theorem seeSaw_iteratedIntegrand_vacuumForm_base_points_alt : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∀ (φ : t.Ch j → GA D (c.X j) → ℂ) (F : GA D (c.V (j + 1 + 1)) → ℂ) Ψ₁ Ψ₂ f z, Ψ₁ = v.Ψ j P₁ 1 a → Ψ₂ = v.Ψ (j + 1) P₂ a a' → f = rTrans (a' * v.b (j + 1 + 1)) F → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => t.integrand j σ h P₁ P₂ φ F (a * q₁.1) (a' * q₂.1)) (w.sc j * w.sc (j + 1) * z) := by
  intro D c v t w hc hv ht hw j σ h P₁ P₂ a ha a' ha' φ F Ψ₁ Ψ₂ f z hΨ₁ hΨ₂ hf hI
  classical
  obtain ⟨-, -, hcomm₁, -, hright₁, -⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨-, -, hcomm₂, -, hright₂, -⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  have hj₁ : j + 1 < D.R.m := by omega
  have hj₂ : j + 1 + 1 < D.R.m := by omega

  have key : ∀ p₁ ∈ GfC (c.V (j + 1)), ∀ p₂ ∈ GfC (c.V (j + 1 + 1)),
      t.integrand j σ h P₁ P₂ φ F (a * (p₁ * v.b (j + 1))) (a' * (p₂ * v.b (j + 1 + 1))) =
        w.sc j * w.sc (j + 1) * ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
            (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
            (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g p₁ p₂) (rTrans p₂ f) := by
    intro p₁ hp₁ p₂ hp₂
    have ec₁ : a * (p₁ * v.b (j + 1)) = p₁ * (a * v.b (j + 1)) := by
      rw [← mul_assoc, hcomm₁ a ha p₁ hp₁, mul_assoc]
    have ec₂ : a' * (p₂ * v.b (j + 1 + 1)) = p₂ * (a' * v.b (j + 1 + 1)) := by
      rw [← mul_assoc, hcomm₂ a' ha' p₂ hp₂, mul_assoc]
    have er : rTrans (a' * (p₂ * v.b (j + 1 + 1))) F = rTrans p₂ f := by
      rw [hf, ec₂]; funext x; simp only [rTrans, mul_assoc]
    unfold Tup.integrand
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [(hw.e j α).1, Finsupp.mapDomain_support_of_injective (mul_left_injective (v.b j)),
      Finset.sum_image (fun x _ y _ hxy => mul_right_cancel hxy), Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finsupp.mapDomain_apply (mul_left_injective (v.b j))]
    have e₁ : (t.sBF j (σ + 1) h).om (g * v.b j, a * (p₁ * v.b (j + 1))) (t.pt j P₁) =
        w.sc j • (t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
      rw [(ht.sBF j (σ + 1) h).1, ec₁,
        show ((g * v.b j, p₁ * (a * v.b (j + 1))) : GA D (c.V j) × GA D (c.V (j + 1))) =
          (g, p₁) * (1 * v.b j, a * v.b (j + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf j hj₁ P₁ 1 (one_mem _) a ha, map_smul, hΨ₁]
    have e₂ : (t.sFB j σ h).om (a * (p₁ * v.b (j + 1)), a' * (p₂ * v.b (j + 1 + 1))) (t.pt (j + 1) P₂) =
        w.sc (j + 1) • (t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
      rw [(ht.sFB j σ h).1, ec₁, ec₂,
        show ((p₁ * (a * v.b (j + 1)), p₂ * (a' * v.b (j + 1 + 1))) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) =
          (p₁, p₂) * (a * v.b (j + 1), a' * v.b (j + 1 + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf (j + 1) hj₂ P₂ a ha a' ha', map_smul, hΨ₂]
    have hh := (GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)).1
    simp only [Chain.hand]
    rw [e₁, e₂, hh, er]
    have hp := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (w.sc j * w.sc (j + 1)) 1
      (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α)
        (flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)))))
        (flatFB (t.sFB j σ h) ((t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)))))
      (rTrans p₂ f)
    rw [one_smul] at hp
    rw [hp]
    ring
  obtain ⟨f₁, h1, h2⟩ := hI
  haveI := hright₁ _ (hc.μf (j + 1))
  haveI := hright₂ _ (hc.μf (j + 1 + 1))
  set B₁ : GfC (c.V (j + 1)) := ⟨v.b (j + 1), hv.b (j + 1)⟩ with hB₁
  set B₂ : GfC (c.V (j + 1 + 1)) := ⟨v.b (j + 1 + 1), hv.b (j + 1 + 1)⟩ with hB₂
  refine ⟨fun q => (w.sc j * w.sc (j + 1)) * f₁ (q * B₁⁻¹), ?_, fun q => ?_⟩
  · exact (h1.mul_right B₁⁻¹).smul (w.sc j * w.sc (j + 1))
  · have := ((h2 (q * B₁⁻¹)).mul_right B₂⁻¹).smul (w.sc j * w.sc (j + 1))
    convert this using 1
    funext q₂
    have eq₁ : (q : GA D (c.V (j + 1))) = ((q * B₁⁻¹ : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) * v.b (j + 1) := by
      simp [hB₁]
    have eq₂ : (q₂ : GA D (c.V (j + 1 + 1))) =
        ((q₂ * B₂⁻¹ : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) * v.b (j + 1 + 1) := by
      simp [hB₂]
    rw [Pi.smul_apply, smul_eq_mul]
    beta_reduce
    rw [eq₁, eq₂]
    exact key _ (q * B₁⁻¹).2 _ (q₂ * B₂⁻¹).2

end GlobalTheory.VMove
