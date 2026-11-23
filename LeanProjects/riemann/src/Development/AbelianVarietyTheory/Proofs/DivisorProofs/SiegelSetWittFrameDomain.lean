import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelContinuousFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBoundStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelTheta

theorem transp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAd σ ((1 : E) • J.map σ)) :
    ∃ a' : UA σ J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • J.map σ) a := by
  have e := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ (c := (1 : E)) one_ne_zero
  refine ⟨⟨HA.mat (AF F) σ ((1 : E) • J.map σ) a, ?_⟩, rfl⟩
  have : HA.mat (AF F) σ ((1 : E) • J.map σ) a ∈ HR (AF F) σ ((1 : E) • J.map σ) := a.2
  rw [← e] at this
  exact this

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {C₀ K : Set (GAd σ J)} (hC₀ : IsCompact C₀) (hK : IsCompact K) :
    ∃ B : ℝ, ∀ x ∈ C₀, ∀ k ∈ K, (heightGL F (HA.mat (AF F) σ J (x * k)) : ℝ) ≤ B := by
  have hc : Continuous fun q : GAd σ J × GAd σ J => (heightGL F (HA.mat (AF F) σ J (q.1 * q.2)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_mul : Continuous fun p : GAd σ J × GAd σ J => p.1 * p.2)))
  obtain ⟨B, hB⟩ := ((hC₀.prod hK).image hc).bddAbove
  exact ⟨B, fun x hx k hk => hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩⟩

end GlobalTheory.SiegelTheta

namespace GlobalTheory.SiegelTheta

theorem theta_le_seminorm_height_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨Bd, hBd⟩ := ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  let I := {q : UA σ W.J × UA σ X.J × GAd σ ((1 : E) • X.J.map σ) × (Fin r₀ → ℝ) × GAd σ ((1 : E) • X.J.map σ) ×
      GAd σ ((1 : E) • X.J.map σ) // q.2.2.1 ∈ Ω ∧ q.2.2.2.1 ∈ GlobalTheory.SiegelSet.cone r₀ c ∧
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf q.2.2.2.1 q.2.2.2.2.1 ∧ q.2.2.2.2.2 ∈ K ∧
      (q.2.1 : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (q.2.2.1 * q.2.2.2.2.1 * q.2.2.2.2.2)}
  have hT := fun q : I => GlobalTheory.T.theta_kernel_continuous_functional F E σ B n d X W M χX χW om r s r' s' hP φ hφ q.1.2.1 q.1.1
  choose T hT using hT
  let P : I → ℝ := fun q => ∏ i, q.1.2.2.2.1 i ^ (Module.finrank ℚ F * d)
  have hP0 : ∀ q : I, 0 < P q := fun q => Finset.prod_pos fun i _ => pow_pos (q.2.2.1.1 i) _
  have hpt : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, ∃ (N : ℕ) (C : ℝ), ∀ q : I,
      ‖((P q)⁻¹ • T q) f‖ ≤ C * (ht q.1.1 : ℝ) ^ N := by
    intro f
    obtain ⟨C₁, k₁, h₁⟩ := GlobalTheory.T.siegel_set_witt_frame_schwartz_bound F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr c hc (pureA F f φ)
      (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
    refine ⟨k₁, |C₁| * (max Bd 0) ^ k₁, fun q => ?_⟩
    obtain ⟨⟨h, g, p, t, a, k⟩, hp, htc, ha, hk, hg⟩ := q
    obtain ⟨a', ha'⟩ := transp hσ X.J a
    have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
        HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
      have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
      rw [this]
      change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
      rw [ha', hg]
      rfl
    have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
      refine le_trans ?_ (le_max_left _ _)
      show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
      rw [hy]
      exact hBd _ (hconj p hp t htc a ha) k hk
    have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
    rw [mul_inv_cancel_left] at hb
    have hPq : 0 < ∏ i, t i ^ (Module.finrank ℚ F * d) := Finset.prod_pos fun i _ => pow_pos (htc.1 i) _
    show ‖((∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ • T _) f‖ ≤ _
    rw [ContinuousLinearMap.smul_apply, ← hT, norm_smul, Real.norm_of_nonneg (inv_pos.2 hPq).le]
    have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
    have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
    calc (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * ‖theta om (pureA F f φ) g h‖
        ≤ (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * (C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ *
            ∏ i, t i ^ (Module.finrank ℚ F * d)) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hPq).le
      _ = C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ := by field_simp
      _ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
            (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
      _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring
  obtain ⟨N, C, S, hN⟩ := GlobalTheory.T.uniform_schwartz_seminorm_bound (Fin n × Fin d → mixedEmbedding.mixedSpace F) I (fun q => (P q)⁻¹ • T q)
    (fun q => (ht q.1.1 : ℝ)) (fun q => NNReal.coe_nonneg _) hpt
  refine ⟨N, C, S, fun f h g p hp t htc a ha k hk hg => ?_⟩
  let q : I := ⟨(h, g, p, t, a, k), hp, htc, ha, hk, hg⟩
  have e1 : theta om (pureA F f φ) g h = P q • ((P q)⁻¹ • T q f) := by
    rw [smul_smul, mul_inv_cancel₀ (hP0 q).ne', one_smul]
    exact hT q f
  have e2 := hN q f
  simp only [ContinuousLinearMap.smul_apply] at e2
  rw [e1, norm_smul, Real.norm_of_nonneg (hP0 q).le]
  calc P q * ‖(P q)⁻¹ • T q f‖ ≤ P q * (C * (S.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left e2 (hP0 q).le
    _ = _ := by ring

end GlobalTheory.SiegelTheta
