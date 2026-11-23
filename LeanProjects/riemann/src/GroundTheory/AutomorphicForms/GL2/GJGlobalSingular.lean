import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfold
import GroundTheory.AutomorphicForms.GL2.GJGlobalMean
import GroundTheory.AutomorphicForms.GL2.GJGlobalRank
import GroundTheory.AutomorphicForms.GL2.GJGlobalMellin

open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem isLeftInvariant_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsLeftInvariant ψ) :
    IsLeftInvariant (fun g => conj (ψ g)) := fun γ g => by
  simp only [h γ g]

theorem isCuspidal_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsCuspidal ψ) :
    IsCuspidal (fun g => conj (ψ g)) := by
  intro r hr hrn g
  have := h r hr hrn g
  unfold constantTerm at this ⊢
  rw [integral_conj, this, map_zero]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem integrableOn_mul_tsum_comp {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    {C : ℝ} (hC : ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C)
    {ι : Type*} [Countable ι] (e : ι → Matrix (Fin n) (Fin n) K) (he : Function.Injective e) :
    IntegrableOn (fun g : normOneGL K n => ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' i, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (e i) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])))
      (fundamentalDomain Γ₁) μ := by
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  refine Measure.integrableOn_of_bounded (M := C) hF.ne ?_ ?_
  · refine ((hψc.comp continuous_subtype_val).measurable.mul ?_).aestronglyMeasurable
    refine UnfoldGL.measurable_tsum_of_summable (fun i => ?_) fun g => ?_
    · exact (hΦ.comp (continuous_const.mul (Units.continuous_val.comp
        continuous_subtype_val))).measurable
    · exact ((hsum g).comp_injective he).of_norm
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hC g g.2)
    refine (norm_tsum_le_tsum_norm ((hsum g).comp_injective he)).trans ?_
    exact Summable.tsum_le_tsum_of_inj e he (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
      ((hsum g).comp_injective he) (hsum g)

set_option maxHeartbeats 800000 in

theorem setIntegral_mul_tsum_det_eq_zero (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ = 0 := by
  obtain ⟨C, hC⟩ := hbd
  have hsplit : ∀ g : normOneGL K n,
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
        ∑ r : Fin n, ψ (g : AdelicGLn.AdelicGL K n) *
          ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
            Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
              ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_det_eq_zero_eq_sum_rank (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, Finset.mul_sum]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_finsetSum _ fun r _ =>
      integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : (r : ℕ) = 0
  ·
    have hmem : (0 : Matrix (Fin n) (Fin n) K).rank = r := by rw [Matrix.rank_zero, hr]
    have h0 : ∀ g : normOneGL K n,
        ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
          Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) = Φ 0 := by
      intro g
      have hu : ∀ ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, ξ = ⟨0, hmem⟩ := by
        intro ξ
        refine Subtype.ext ?_
        have h1 : (ξ : Matrix (Fin n) (Fin n) K).rank = 0 := ξ.2.trans hr
        exact (rank_eq_zero_iff (K := K) (n := n)).1 h1
      rw [tsum_eq_single (⟨0, hmem⟩ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r})
        fun ξ hξ => absurd (hu ξ) hξ]
      have hz : ratMat (0 : Matrix (Fin n) (Fin n) K) = 0 := by
        unfold ratMat
        exact Matrix.map_zero _ (map_zero _)
      rw [hz, mul_zero, zero_mul]
    have hm := setIntegral_fundamentalDomain_eq_zero μ hn hψc hψl hψ hψb
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => by rw [h0 g],
      integral_mul_const, hm, zero_mul]
  ·
    have hk : 0 < n - (r : ℕ) := Nat.sub_pos_of_lt r.2
    have hkn : n - (r : ℕ) < n := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero hr)
    have e : n - (n - (r : ℕ)) = r := Nat.sub_sub_self r.2.le
    have := UnfoldGL.setIntegral_mul_tsum_rank_eq_zero μ hψc hψl hψ hΦ y hsum ⟨C, hC⟩ hk hkn
    rw [e] at this
    exact this

set_option maxHeartbeats 800000 in

theorem setIntegral_mul_tsum_eq_tsum_GL (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ =
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ := by
  obtain ⟨C, hC⟩ := hbd
  have hsing := setIntegral_mul_tsum_det_eq_zero μ hn hψc hψl hψ hψb hΦ y hsum ⟨C, hC⟩
  have hsplit : ∀ g : normOneGL K n, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K,
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) +
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_eq_tsum_GL_add (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, mul_add]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_add (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Units.val_injective)
      (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective), hsing, add_zero]

end GJGlobal

end

end GroundTheory.Automorphic
