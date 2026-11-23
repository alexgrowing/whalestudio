import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefContinuousCompactNormEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeModelGramNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormCompactBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureCompactBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CurvInterp

open GlobalTheory.HermFrame

theorem opNorm_le_entries {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hb : ∀ v : Fin n → ℂ, c * ‖v‖ ≤ gnorm H v ∧ gnorm H v ≤ C * ‖v‖)
    (M : Matrix (Fin n) (Fin n) ℂ) : opNorm H H M ≤ C / c * ∑ a, ∑ b, ‖M a b‖ := by
  have hN : 0 ≤ ∑ a, ∑ b, ‖M a b‖ := by positivity
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  have h1 : ‖M *ᵥ v‖ ≤ (∑ a, ∑ b, ‖M a b‖) * ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
    calc ‖(M *ᵥ v) a‖ = ‖∑ b, M a b * v b‖ := rfl
      _ ≤ ∑ b, ‖M a b‖ * ‖v‖ := norm_sum_le_of_le _ fun b _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v b) (norm_nonneg _)
      _ = (∑ b, ‖M a b‖) * ‖v‖ := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun a => ∑ b, ‖M a b‖)
          (fun _ _ => by positivity) (Finset.mem_univ a)) (norm_nonneg _)
  have h3 : ‖v‖ ≤ gnorm H v / c := by rw [le_div_iff₀ hc]; linarith [(hb v).1]
  calc gnorm H (M *ᵥ v) ≤ C * ‖M *ᵥ v‖ := (hb _).2
    _ ≤ C * ((∑ a, ∑ b, ‖M a b‖) * ‖v‖) := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * ((∑ a, ∑ b, ‖M a b‖) * (gnorm H v / c)) := by gcongr
    _ = C / c * (∑ a, ∑ b, ‖M a b‖) * gnorm H v := by ring

theorem opNorm_le_of_comparable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (h : ∀ v, a * gnorm A v ≤ gnorm B v ∧ gnorm B v ≤ b * gnorm A v)
    (T : Matrix (Fin n) (Fin n) ℂ) : opNorm B B T ≤ b / a * opNorm A A T := by
  have hT := opNorm_nonneg A A T
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  have h2 := gnorm_mulVec_le hA hA.posSemidef T v
  have h3 : gnorm A v ≤ gnorm B v / a := by rw [le_div_iff₀ ha]; linarith [(h v).1]
  calc gnorm B (T *ᵥ v) ≤ b * gnorm A (T *ᵥ v) := (h _).2
    _ ≤ b * (opNorm A A T * gnorm A v) := mul_le_mul_of_nonneg_left h2 hb
    _ ≤ b * (opNorm A A T * (gnorm B v / a)) := by gcongr
    _ = b / a * opNorm A A T * gnorm B v := by ring

theorem bound_conn_sub_curv : ∀ (e m n : ℕ) (σ : Fin m → Option (Fin e)) (ρ C : ℝ)
    (H₀ H : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), 0 < ρ →
    GlobalTheory.HermFrame.IsPosFrame (Metric.ball 0 ρ) H₀ →
    GlobalTheory.HermFrame.OneFormBound (punct σ ρ) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (modelGram σ)
      (GlobalTheory.HermFrame.conn H) C →
    ∃ ρ' C' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧
      GlobalTheory.HermFrame.OneFormBound (punct σ ρ') H₀ (modelGram σ)
        (fun z ξ => GlobalTheory.HermFrame.conn H z ξ - GlobalTheory.HermFrame.conn H₀ z ξ) C' ∧
      GlobalTheory.HermFrame.TwoFormBound (punct σ ρ') H₀ (modelGram σ) (GlobalTheory.HermFrame.curv H₀) C' := by
  intro e m n σ ρ C H₀ H hρ hH₀ hH
  have hρ'0 : 0 < min (ρ / 2) (1 / 2 : ℝ) := lt_min (by linarith) (by norm_num)
  have hρ'ρ : min (ρ / 2) (1 / 2 : ℝ) < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hρ'h : min (ρ / 2) (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
  set ρ' := min (ρ / 2) (1 / 2 : ℝ)
  have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) ρ') := isCompact_closedBall _ _
  have hKU : Metric.closedBall (0 : Fin e → ℂ) ρ' ⊆ Metric.ball 0 ρ :=
    Metric.closedBall_subset_ball hρ'ρ
  have hcK : ContinuousOn H₀ (Metric.closedBall (0 : Fin e → ℂ) ρ') := by
    intro z hz
    exact continuousWithinAt_pi.2 fun a => continuousWithinAt_pi.2 fun b =>
      ((hH₀.smooth a b).continuousOn z (hKU hz)).mono hKU
  obtain ⟨c, Cu, hc, hCu, hb⟩ := GlobalTheory.T.pos_def_continuous_compact_norm_equiv e n _ H₀ hK hcK
    fun z hz => hH₀.posDef z (hKU hz)
  obtain ⟨c₁, C₁, hc₁, hC₁, hb₁⟩ := GlobalTheory.T.pos_def_continuous_compact_norm_equiv e n {0}
    (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) isCompact_singleton continuousOn_const
    fun _ _ => PosDef.one
  obtain ⟨B₁, hB₁, hconn⟩ := GlobalTheory.T.connection_form_compact_bound e n _ _ H₀ hH₀ hK hKU
  obtain ⟨B₂, hB₂, hcurv⟩ := GlobalTheory.T.curvature_compact_bound e n _ _ H₀ hH₀ hK hKU
  have hsub : punct σ ρ' ⊆ Metric.closedBall 0 ρ' := fun z hz => Metric.ball_subset_closedBall hz.1
  have hsubρ : punct σ ρ' ⊆ punct σ ρ := punct_mono σ hρ'ρ.le
  have hsubh : punct σ ρ' ⊆ punct σ (1 / 2) := punct_mono σ hρ'h

  have hcmp : ∀ z ∈ Metric.closedBall (0 : Fin e → ℂ) ρ', ∀ v : Fin n → ℂ,
      c / C₁ * gnorm 1 v ≤ gnorm (H₀ z) v ∧ gnorm (H₀ z) v ≤ Cu / c₁ * gnorm 1 v := by
    intro z hz v
    obtain ⟨h1, h2⟩ := hb z hz v
    obtain ⟨h3, h4⟩ := hb₁ 0 rfl v
    constructor
    · calc c / C₁ * gnorm 1 v ≤ c / C₁ * (C₁ * ‖v‖) := by gcongr
        _ = c * ‖v‖ := by field_simp
        _ ≤ _ := h1
    · calc gnorm (H₀ z) v ≤ Cu * ‖v‖ := h2
        _ = Cu / c₁ * (c₁ * ‖v‖) := by field_simp
        _ ≤ Cu / c₁ * gnorm 1 v := by gcongr
  set K₁ := Cu / c₁ / (c / C₁) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ Cu / c * B₁ := by positivity
  have hK₃0 : 0 ≤ Cu / c * B₂ := by positivity
  refine ⟨ρ', K₁ * max C 0 + Cu / c * B₁ + Cu / c * B₂, hρ'0, hρ'ρ.le, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨-, hG, hbd⟩ := hH z (hsubρ hz)
    have hp := hH₀.posDef z (hKU (hsub hz))
    refine ⟨hp, hG, fun ξ => ?_⟩
    have hg := GlobalTheory.T.norm_le_model_gram_norm e m σ z (hsubh hz) ξ
    have hg0 := gnorm_nonneg (modelGram σ z) ξ
    have e1 : opNorm (H₀ z) (H₀ z) (conn H z ξ) ≤ K₁ * max C 0 * gnorm (modelGram σ z) ξ :=
      calc opNorm (H₀ z) (H₀ z) (conn H z ξ) ≤ K₁ * opNorm 1 1 (conn H z ξ) :=
            opNorm_le_of_comparable PosDef.one (by positivity) (by positivity) (hcmp z (hsub hz)) _
        _ ≤ K₁ * (C * gnorm (modelGram σ z) ξ) := mul_le_mul_of_nonneg_left (hbd ξ) hK₁0
        _ ≤ K₁ * (max C 0 * gnorm (modelGram σ z) ξ) := by
            gcongr; exact le_max_left _ _
        _ = _ := by ring
    have e2 : opNorm (H₀ z) (H₀ z) (-conn H₀ z ξ) ≤ Cu / c * B₁ * gnorm (modelGram σ z) ξ :=
      calc opNorm (H₀ z) (H₀ z) (-conn H₀ z ξ) ≤ Cu / c * ∑ a, ∑ b, ‖(-conn H₀ z ξ) a b‖ :=
            opNorm_le_entries hc hCu.le (hb z (hsub hz)) _
        _ = Cu / c * ∑ a, ∑ b, ‖conn H₀ z ξ a b‖ := by simp
        _ ≤ Cu / c * (B₁ * ‖ξ‖) := by gcongr; exact hconn z (hsub hz) ξ
        _ ≤ Cu / c * (B₁ * gnorm (modelGram σ z) ξ) := by gcongr
        _ = _ := by ring
    show opNorm (H₀ z) (H₀ z) (conn H z ξ - conn H₀ z ξ) ≤ _
    rw [sub_eq_add_neg]
    refine (opNorm_add_le hp hp.posSemidef _ _).trans ?_
    have : 0 ≤ Cu / c * B₂ * gnorm (modelGram σ z) ξ := by positivity
    nlinarith
  · have hG := modelGram_posSemidef σ z
    have hp := hH₀.posDef z (hKU (hsub hz))
    refine ⟨hp, hG, fun ξ η => ?_⟩
    have hg := GlobalTheory.T.norm_le_model_gram_norm e m σ z (hsubh hz) ξ
    have hg' := GlobalTheory.T.norm_le_model_gram_norm e m σ z (hsubh hz) η
    have hg0 := gnorm_nonneg (modelGram σ z) ξ
    have hg0' := gnorm_nonneg (modelGram σ z) η
    have e3 : opNorm (H₀ z) (H₀ z) (curv H₀ z ξ η) ≤
        Cu / c * B₂ * gnorm (modelGram σ z) ξ * gnorm (modelGram σ z) η :=
      calc opNorm (H₀ z) (H₀ z) (curv H₀ z ξ η) ≤ Cu / c * ∑ a, ∑ b, ‖curv H₀ z ξ η a b‖ :=
            opNorm_le_entries hc hCu.le (hb z (hsub hz)) _
        _ ≤ Cu / c * (B₂ * ‖ξ‖ * ‖η‖) := by gcongr; exact hcurv z (hsub hz) ξ η
        _ ≤ Cu / c * (B₂ * gnorm (modelGram σ z) ξ * gnorm (modelGram σ z) η) := by gcongr
        _ = _ := by ring
    have : 0 ≤ (K₁ * max C 0 + Cu / c * B₁) * (gnorm (modelGram σ z) ξ * gnorm (modelGram σ z) η) := by
      positivity
    nlinarith

end GlobalTheory.CurvInterp
