import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.RealInd

theorem exists_kLevi_equivariant_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ φ : UJ ε → D.V,
    Continuous φ ∧ φ 1 ≠ 0 ∧
    ∀ m ∈ leviOne ε D.W, m ∈ KG ε → ∀ g, φ (m * g) = D.σ (uMat m) (φ g) := by
  intro n ε D
  obtain ⟨hnt, -, hU, -⟩ := D.temp
  let C : Subgroup (UJ ε) := KG ε ⊓ leviOne ε D.W
  have hC : IsCompact (C : Set (UJ ε)) :=
    (isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne D.flag D.pos)
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let μ : Measure C := Measure.haarMeasure ⊤
  obtain ⟨v, hv⟩ := exists_ne (0 : D.V)
  have hmat : ∀ c : C, uMat (c : UJ ε) ∈ mats (leviOne ε D.W) := fun c => ⟨c, c.2.2, rfl⟩
  have hsc : Continuous fun c : C => D.σ (uMat (c : UJ ε)) v :=
    (hU.2.2 v).comp_continuous (continuous_uMat.comp continuous_subtype_val) hmat
  have hσ1 : D.σ (uMat (1 : UJ ε)) v = v := by rw [uMat_one, hU.1.1]; rfl

  have hS : IsOpen {c : C | 0 < RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ} :=
    isOpen_lt continuous_const (RCLike.continuous_re.comp (continuous_const.inner hsc))
  obtain ⟨U, hUo, hUS⟩ := isOpen_induced_iff.1 hS
  have h1U : (1 : UJ ε) ∈ U := by
    have : (1 : C) ∈ Subtype.val ⁻¹' U := by
      rw [hUS]
      change 0 < RCLike.re ⟪v, D.σ (uMat (1 : UJ ε)) v⟫_ℂ
      rw [hσ1, inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.2 hv) 2
    exact this
  obtain ⟨f, hf, hf1, hfK⟩ := CompletelyRegularSpace.completely_regular (1 : UJ ε) Uᶜ hUo.isClosed_compl
    (fun h => h h1U)
  let b : UJ ε → ℝ := fun g => 1 - (f g : ℝ)
  have hb : Continuous b := continuous_const.sub (continuous_subtype_val.comp hf)
  have hb0 : ∀ g, 0 ≤ b g := fun g => sub_nonneg.2 (f g).2.2
  have hb1 : b 1 = 1 := by simp [b, hf1]
  have hbU : ∀ g, b g ≠ 0 → g ∈ U := fun g hg => by
    by_contra h
    exact hg (by simp [b, hfK h])
  let F : UJ ε → C → D.V := fun g c => ((b (g⁻¹ * c) : ℝ) : ℂ) • D.σ (uMat (c : UJ ε)) v
  have hF : Continuous (Function.uncurry F) :=
    (Complex.continuous_ofReal.comp (hb.comp (continuous_fst.inv.mul
      (continuous_subtype_val.comp continuous_snd)))).smul (hsc.comp continuous_snd)
  have hFi : ∀ g, Integrable (F g) μ := fun g =>
    (hF.comp (Continuous.prodMk_right g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨fun g => ∫ c, F g c ∂μ, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := μ) hF (isCompact_univ (X := C))
    simpa only [Measure.restrict_univ] using this
  · intro h0
    beta_reduce at h0
    have e1 : ∫ c, ⟪v, F 1 c⟫_ℂ ∂μ = 0 := by rw [integral_inner (hFi 1), h0, inner_zero_right]
    have e2 : ∫ c, RCLike.re ⟪v, F 1 c⟫_ℂ ∂μ = 0 := by
      rw [integral_re ((hFi 1).const_inner v), e1, map_zero]
    let G : C → ℝ := fun c => b c * RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ
    have eG : ∀ c, RCLike.re ⟪v, F 1 c⟫_ℂ = G c := fun c => by
      simp only [F, G, inv_one, one_mul, inner_smul_right]
      simp
    have hG : Continuous G :=
      (hb.comp continuous_subtype_val).mul (RCLike.continuous_re.comp (continuous_const.inner hsc))
    have hG0 : 0 ≤ G := fun c => by
      by_cases h : b c = 0
      · simp [G, h]
      · have hc : c ∈ Subtype.val ⁻¹' U := hbU _ h
        rw [hUS] at hc
        exact mul_nonneg (hb0 _) hc.le
    have hG1 : G 1 ≠ 0 := by
      have : G 1 = ‖v‖ ^ 2 := by
        simp only [G]
        rw [show ((1 : C) : UJ ε) = 1 from rfl, hb1, hσ1, inner_self_eq_norm_sq, one_mul]
      rw [this]
      exact (pow_pos (norm_pos_iff.2 hv) 2).ne'
    have := hG.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (HasCompactSupport.of_compactSpace _) hG0 hG1
    rw [← integral_congr_ae (Filter.Eventually.of_forall eG), e2] at this
    exact lt_irrefl _ this
  · intro m hmM hmK g
    let m' : C := ⟨m, hmK, hmM⟩
    beta_reduce
    have e := integral_mul_left_eq_self (μ := μ) (F (m * g)) m'
    rw [← e, ← ContinuousLinearMap.integral_comp_comm _ (hFi g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [F]
    have h1 : (m * g)⁻¹ * ((m' * c : C) : UJ ε) = g⁻¹ * (c : UJ ε) := by
      change (m * g)⁻¹ * (m * (c : UJ ε)) = _
      group
    have h2 : D.σ (uMat ((m' * c : C) : UJ ε)) = D.σ (uMat m) ∘SL D.σ (uMat (c : UJ ε)) := by
      change D.σ (uMat (m * (c : UJ ε))) = _
      rw [uMat_mul]
      exact hU.1.2 _ ⟨m, hmM, rfl⟩ _ (hmat c)
    rw [h1, h2, map_smul]
    rfl

end GlobalTheory.RealInd
