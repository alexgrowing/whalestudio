import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBound

open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.RealWeil.SchrFamily

variable {l : Type} [Fintype l]

def pCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := pPart, map_add' := pPart_add, map_smul' := pPart_smul }

def qCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := qPart, map_add' := qPart_add, map_smul' := qPart_smul }

theorem rhoSch_eq (w : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2))
      (SchwartzMap.compSubConstCLM ℂ (-pPart w) g) := by
  ext x
  rw [coe_rhoSch, SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase _ _),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, rhoFun, phase_eq_eChar, sub_neg_eq_add]
  simp

theorem seminorm_rhoSch_sub_le (p : Seminorm ℂ (Sch l)) (hp : Continuous p) :
    ∃ (q₁ q₂ q₃ : Seminorm ℂ (Sch l)) (M₁ M₂ M₃ : ℕ), ∀ (w : l ⊕ l → ℝ) (g : Sch l),
      p (rhoSch w g - g) ≤ (‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2|) * (1 + ‖qPart w‖) ^ M₁ *
          (‖pPart w‖ * (1 + ‖pPart w‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart w‖ * (1 + ‖pPart w‖) ^ M₂ * q₂ g := by
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) q₁ hq₁
  refine ⟨q₁, q₂, q₃, M₁, M₂, M₃, fun w g => ?_⟩
  set T := SchwartzMap.compSubConstCLM ℂ (-pPart w) g with hT
  have hL : ‖innerSL ℝ (qPart w)‖ = ‖qPart w‖ := innerSL_apply_norm _ _
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2)) T - T) (T - g)
  rw [sub_add_sub_cancel] at h1
  rw [rhoSch_eq]
  refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
  rw [hL]
  have h2 := map_add_le_add q₁ (T - g) g
  rw [sub_add_cancel] at h2
  have h3 := hb₃ (pPart w) g
  gcongr
  linarith

theorem tendsto_rhoSch_zero (g : Sch l) : Tendsto (fun u => rhoSch u g) (𝓝 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds _ g]
  intro i ε hε
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (schwartzSeminormFamily ℂ _ ℂ i)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm i)
  have hpc : Tendsto (fun u : l ⊕ l → ℝ => pPart u) (𝓝 0) (𝓝 0) := by
    have := (pCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hqc : Tendsto (fun u : l ⊕ l → ℝ => qPart u) (𝓝 0) (𝓝 0) := by
    have := (qCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hpn : Tendsto (fun u : l ⊕ l → ℝ => ‖pPart u‖) (𝓝 0) (𝓝 0) := by simpa using hpc.norm
  have hqn : Tendsto (fun u : l ⊕ l → ℝ => ‖qPart u‖) (𝓝 0) (𝓝 0) := by simpa using hqc.norm
  have hk : Tendsto (fun u : l ⊕ l → ℝ => |⟪pPart u, qPart u⟫ / 2|) (𝓝 0) (𝓝 0) := by
    have := ((hpc.inner (𝕜 := ℝ) hqc).div_const 2).abs
    simpa using this
  have lim : Tendsto (fun u : l ⊕ l → ℝ => (‖qPart u‖ + |⟪pPart u, qPart u⟫ / 2|) * (1 + ‖qPart u‖) ^ M₁ *
          (‖pPart u‖ * (1 + ‖pPart u‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart u‖ * (1 + ‖pPart u‖) ^ M₂ * q₂ g)
      (𝓝 0) (𝓝 0) := by
    have := (((hqn.add hk).mul ((hqn.const_add 1).pow M₁)).mul
      (((hpn.mul ((hpn.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add
      ((hpn.mul ((hpn.const_add 1).pow M₂)).mul_const (q₂ g))
    simpa using this
  filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu
  exact (hb u g).trans_lt hu

theorem rhoSch_rhoSch (w₀ u : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w₀ (rhoSch u g) = Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) • rhoSch (w₀ + u) g := by
  ext x
  rw [coe_rhoSch, coe_rhoSch, rhoFun_rhoFun, SchwartzMap.smul_apply, coe_rhoSch]
  rfl

theorem continuous_rhoSch (g : Sch l) : Continuous fun w => rhoSch w g := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  set c : (l ⊕ l → ℝ) → ℂ := fun u => Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) with hcdef
  have hs : Continuous fun u : l ⊕ l → ℝ => sympl w₀ u := by
    have e : (fun u : l ⊕ l → ℝ => sympl w₀ u) =
        fun u => ⟪pPart w₀, qCLM l u⟫ - ⟪qPart w₀, pCLM l u⟫ := rfl
    rw [e]
    exact (continuous_const.inner (qCLM l).continuous).sub (continuous_const.inner (pCLM l).continuous)
  have hc : Continuous c := by
    rw [hcdef]
    fun_prop
  have h1 : Tendsto (fun u => (c u)⁻¹ • rhoSch w₀ (rhoSch u g)) (𝓝 0) (𝓝 ((c 0)⁻¹ • rhoSch w₀ g)) :=
    ((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul
      (((rhoSch w₀).continuous.tendsto g).comp (tendsto_rhoSch_zero g))
  have hq0 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hp0 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hc0 : c 0 = 1 := by simp [hcdef, sympl, hq0, hp0]
  have e : ∀ u, (c u)⁻¹ • rhoSch w₀ (rhoSch u g) = rhoSch (w₀ + u) g := fun u => by
    rw [rhoSch_rhoSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]
  simp only [e, hc0, inv_one, one_smul] at h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  refine (h1.comp h3).congr fun w => ?_
  simp

theorem seminorm_rhoSch_le (g : Sch l) (k m : ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (rhoSch w g) ≤ C * (1 + ‖w‖) ^ N := by
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (SchwartzMap.seminorm ℂ k m)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm (k, m))
  set p := SchwartzMap.seminorm ℂ k m (E := EuclideanSpace ℝ l) (F := ℂ) with hpdef
  set c := ‖pCLM l‖ + ‖qCLM l‖ with hcdef
  set N := 3 + M₁ + M₂ + M₃ with hN
  have hq1 : 0 ≤ q₁ g := apply_nonneg _ _
  have hq2 : 0 ≤ q₂ g := apply_nonneg _ _
  have hq3 : 0 ≤ q₃ g := apply_nonneg _ _
  have hp : 0 ≤ p g := apply_nonneg _ _
  refine ⟨(1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g), N, fun w => ?_⟩
  have hc : 0 ≤ c := by positivity
  have hw := norm_nonneg w
  set X := (1 + c) * (1 + ‖w‖) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hpw : ‖pPart w‖ ≤ ‖pCLM l‖ * ‖w‖ := (pCLM l).le_opNorm w
  have hqw : ‖qPart w‖ ≤ ‖qCLM l‖ * ‖w‖ := (qCLM l).le_opNorm w
  have hpn := norm_nonneg (pCLM l)
  have hqn := norm_nonneg (qCLM l)
  have ha : 1 + ‖pPart w‖ ≤ X := by rw [hX]; nlinarith
  have hb' : 1 + ‖qPart w‖ ≤ X := by rw [hX]; nlinarith
  have ha' : ‖pPart w‖ ≤ X := by linarith
  have hb'' : ‖qPart w‖ ≤ X := by linarith
  have hk : ‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2| ≤ 2 * X ^ 2 := by
    have h1 : |⟪pPart w, qPart w⟫| ≤ ‖pPart w‖ * ‖qPart w‖ := abs_real_inner_le_norm _ _
    have h2 : ‖pPart w‖ * ‖qPart w‖ ≤ X * X := mul_le_mul ha' hb'' (norm_nonneg _) (by linarith)
    rw [abs_div, abs_two]
    nlinarith
  have hsub : p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := by
    simpa using map_add_le_add p (rhoSch w g - g) g
  calc p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := hsub
    _ ≤ (2 * X ^ 2) * X ^ M₁ * (X * X ^ M₃ * q₃ g + q₁ g) + X * X ^ M₂ * q₂ g + p g := by
        refine add_le_add ((hb w g).trans ?_) le_rfl
        gcongr
    _ = 2 * X ^ (3 + M₁ + M₃) * q₃ g + 2 * X ^ (2 + M₁) * q₁ g + X ^ (1 + M₂) * q₂ g + 1 * p g := by ring
    _ ≤ 2 * X ^ N * q₃ g + 2 * X ^ N * q₁ g + X ^ N * q₂ g + X ^ N * p g := by
        have e1 : X ^ (3 + M₁ + M₃) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e2 : X ^ (2 + M₁) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e3 : X ^ (1 + M₂) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e4 : (1 : ℝ) ≤ X ^ N := one_le_pow₀ hX1
        have f1 := mul_le_mul_of_nonneg_right e1 hq3
        have f2 := mul_le_mul_of_nonneg_right e2 hq1
        have f3 := mul_le_mul_of_nonneg_right e3 hq2
        have f4 := mul_le_mul_of_nonneg_right e4 hp
        nlinarith
    _ = (1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g) * (1 + ‖w‖) ^ N := by
        rw [hX, mul_pow]; ring

theorem exists_continuous_schwartz_rhoFun : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n),
    Continuous G ∧ (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N :=
  fun _ f => ⟨fun w => rhoSch w f, continuous_rhoSch f, fun w => coe_rhoSch w f, seminorm_rhoSch_le f⟩

end GlobalTheory.RealWeil.SchrFamily
