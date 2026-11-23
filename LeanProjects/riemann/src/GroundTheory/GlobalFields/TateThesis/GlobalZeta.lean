import Mathlib
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite
import GroundTheory.GlobalFields.TateThesis.HeckeChar

open NumberField IsDedekindDomain Topology Filter MeasureTheory NumberField.mixedEmbedding Metric
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap nonZeroDivisors Classical

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem continuous_of_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact (φ.continuous.comp ((homeomorphMixedSpace K).continuous.comp continuous_fst)).mul
      (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

theorem continuous_ideleModule_val : Continuous fun x : IdeleGroup K ↦ (ideleModule K x : ℝ) :=
  continuous_subtype_val.comp continuous_ideleModule

theorem infiniteZetaBound_nonneg (σ : ℝ) (k : ℕ) (a : (InfiniteAdeleRing K)ˣ) :
    0 ≤ infiniteZetaBound σ k a :=
  Finset.prod_nonneg fun w _ ↦ by positivity

theorem ideleModule_rpow_eq (x : IdeleGroup K) (σ : ℝ) :
    (ideleModule K x : ℝ) ^ σ = (∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) :
      InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) * finiteModule (ofFinite (toFinite K x)) ^ σ := by
  rw [ideleModule_apply, Real.mul_rpow (infiniteModule_pos x).le (finiteModule_pos x).le,
    infiniteModule, ← Real.finsetProd_rpow _ _ (fun w _ ↦ by positivity)]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  rfl

theorem exists_bound_schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ))
    {g : FiniteAdeleRing (𝓞 K) K → ℂ} (hg : g ∈ finiteSchwartzBruhat K) (σ : ℝ) :
    ∃ C : ℝ, ∃ k : ℕ, ∃ L : (FractionalIdeal (𝓞 K)⁰ K)ˣ, 0 ≤ C ∧ 2 * σ + 2 < k ∧
      ∀ x : IdeleGroup K, ‖schwartzBruhatTensor φ g (x : 𝔸[K])‖ * (ideleModule K x : ℝ) ^ σ ≤
        C * (infiniteZetaBound σ k (toInfinite K x) * finiteZetaBound L σ (toFinite K x)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * σ + 2 < k := exists_nat_gt _
  obtain ⟨C₁, hC₁, hφ⟩ := exists_norm_schwartz_le_prod φ k
  obtain ⟨M, hM⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hg.2
  refine ⟨C₁ * max M 0, k, L, by positivity, hk, fun x ↦ ?_⟩
  set a := toInfinite K x
  set b := toFinite K x
  have hinf : ‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ *
      ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) ≤ C₁ * infiniteZetaBound σ k a := by
    calc ‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ *
          ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)
        ≤ (C₁ * ∏ w, ((1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k)⁻¹) *
            ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) :=
          mul_le_mul_of_nonneg_right (hφ _) (Finset.prod_nonneg fun w _ ↦ by positivity)
      _ = C₁ * infiniteZetaBound σ k a := by
          rw [mul_assoc, ← Finset.prod_mul_distrib, infiniteZetaBound]
          congr 1
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          rw [div_eq_mul_inv, mul_comm]
  have hI := infiniteZetaBound_nonneg σ k a
  unfold schwartzBruhatTensor
  by_cases hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L
  · have hfz : finiteZetaBound L σ b = finiteModule (ofFinite b) ^ σ := by
      rw [finiteZetaBound, if_pos hb]
    rw [hfz, ideleModule_rpow_eq, norm_mul]
    have hgM : ‖g (x : 𝔸[K]).2‖ ≤ max M 0 := (hM _).trans (le_max_left _ _)
    have hfm : 0 ≤ finiteModule (ofFinite b) ^ σ := by
      have := finiteModule_pos (ofFinite b)
      positivity
    calc ‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ * ‖g (x : 𝔸[K]).2‖ *
          ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) *
            finiteModule (ofFinite b) ^ σ)
        = (‖φ (homeomorphMixedSpace K (x : 𝔸[K]).1)‖ *
            ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) * ‖g (x : 𝔸[K]).2‖ *
              finiteModule (ofFinite b) ^ σ := by ring
      _ ≤ (C₁ * infiniteZetaBound σ k a) * max M 0 * finiteModule (ofFinite b) ^ σ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hinf hgM (norm_nonneg _) (mul_nonneg hC₁ hI)) hfm
      _ = C₁ * max M 0 * (infiniteZetaBound σ k a * finiteModule (ofFinite b) ^ σ) := by ring
  · have hg0 : g (x : 𝔸[K]).2 = 0 := by
      by_contra h
      exact hb (hL (subset_tsupport g h))
    rw [hg0, mul_zero, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (mul_nonneg hI (finiteZetaBound_nonneg _ _ _))

theorem integrable_zetaBound {σ : ℝ} (hσ : 1 < σ) {k : ℕ} (hk : 2 * σ + 2 < k)
    (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Integrable (fun x : IdeleGroup K ↦
      infiniteZetaBound σ k (toInfinite K x) * finiteZetaBound L σ (toFinite K x))
      (ideleMeasure K) := by
  have h := (integrable_infiniteZetaBound (K := K) hσ.le hk).mul_prod
    (integrable_finiteZetaBound L hσ)
  exact ((measurePreserving_prodEquiv K).integrable_comp_emb
    (prodEquiv K).toHomeomorph.measurableEmbedding).2 h

theorem continuous_norm_mul_rpow {F : 𝔸[K] → ℂ} (hF : Continuous F) {σ : ℝ} (hσ : 0 ≤ σ) :
    Continuous fun x : IdeleGroup K ↦ ‖F x‖ * (ideleModule K x : ℝ) ^ σ :=
  (hF.comp Units.continuous_val).norm.mul
    (continuous_ideleModule_val.rpow_const fun _ ↦ Or.inr hσ)

theorem integrable_norm_mul_rpow {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {σ : ℝ}
    (hσ : 1 < σ) :
    Integrable (fun x : IdeleGroup K ↦ ‖F x‖ * (ideleModule K x : ℝ) ^ σ) (ideleMeasure K) := by
  have hcont : ∀ {G : 𝔸[K] → ℂ}, G ∈ schwartzBruhat K →
      AEStronglyMeasurable (fun x : IdeleGroup K ↦ ‖G x‖ * (ideleModule K x : ℝ) ^ σ)
        (ideleMeasure K) := fun hG ↦
    (continuous_norm_mul_rpow (continuous_of_mem_schwartzBruhat hG) (by linarith)).aestronglyMeasurable
  have hpow : ∀ x : IdeleGroup K, 0 ≤ (ideleModule K x : ℝ) ^ σ := fun x ↦
    Real.rpow_nonneg (ideleModule K x).2.le σ
  have hmem := hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨C, k, L, hC, hk, hb⟩ := exists_bound_schwartzBruhatTensor φ hg σ
    refine Integrable.mono' ((integrable_zetaBound hσ hk L).const_mul C) (hcont hmem)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hpow x))]
    exact hb x
  | zero =>
    simp only [Pi.zero_apply, norm_zero, zero_mul]
    exact integrable_zero _ _ _
  | add G H hGm hHm hG hH =>
    refine Integrable.mono' ((hG hGm).add (hH hHm)) (hcont hmem) (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hpow x))]
    show ‖G x + H x‖ * _ ≤ ‖G x‖ * _ + ‖H x‖ * _
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hpow x)
  | smul c G hGm hG =>
    convert (hG hGm).const_mul ‖c‖ using 1
    funext x
    simp [mul_assoc]

def globalZeta (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∫ x, f x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s ∂ideleMeasure K

theorem continuous_zetaIntegrand {F : 𝔸[K] → ℂ} (hF : Continuous F) (χ : HeckeCharacter K)
    (s : ℂ) :
    Continuous fun x : IdeleGroup K ↦ F x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s :=
  ((hF.comp Units.continuous_val).mul (continuous_subtype_val.comp χ.continuous_toIdele)).mul
    ((Complex.continuous_ofReal.comp continuous_ideleModule_val).cpow continuous_const
      fun x ↦ Complex.ofReal_mem_slitPlane.2 (ideleModule K x).2)

theorem norm_zetaIntegrand (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (s : ℂ) (x : IdeleGroup K) :
    ‖F x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s‖ =
      ‖F x‖ * (ideleModule K x : ℝ) ^ s.re := by
  rw [norm_mul, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule K x).2]

theorem integrable_globalZetaIntegrand {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : IdeleGroup K ↦ F x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s)
      (ideleMeasure K) := by
  refine (integrable_norm_mul_rpow hF hs).mono'
    (continuous_zetaIntegrand (continuous_of_mem_schwartzBruhat hF) χ s).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_zetaIntegrand]

theorem rpow_mul_abs_log_le {t σ₀ δ σ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hσ : |σ - σ₀| < δ) :
    t ^ σ * |Real.log t| ≤ (t ^ (σ₀ - 2 * δ) + t ^ (σ₀ + 2 * δ)) / δ := by
  have hσ' := abs_lt.1 hσ
  rcases le_or_gt 1 t with h1 | h1
  · have hlog : |Real.log t| ≤ t ^ δ / δ := by
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      exact Real.log_le_rpow_div ht.le hδ
    have hpow : t ^ σ ≤ t ^ (σ₀ + δ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc t ^ σ * |Real.log t| ≤ t ^ (σ₀ + δ) * (t ^ δ / δ) :=
          mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
      _ = t ^ (σ₀ + 2 * δ) / δ := by
          rw [mul_div_assoc', ← Real.rpow_add ht]
          congr 2
          ring
      _ ≤ (t ^ (σ₀ - 2 * δ) + t ^ (σ₀ + 2 * δ)) / δ :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hδ.le
  · have hlog : |Real.log t| ≤ t ^ (-δ) / δ := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le h1.le)]
      have := Real.log_le_rpow_div (inv_nonneg.2 ht.le) hδ
      rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
    have hpow : t ^ σ ≤ t ^ (σ₀ - δ) :=
      Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith)
    calc t ^ σ * |Real.log t| ≤ t ^ (σ₀ - δ) * (t ^ (-δ) / δ) :=
          mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
      _ = t ^ (σ₀ - 2 * δ) / δ := by
          rw [mul_div_assoc', ← Real.rpow_add ht]
          congr 2
          ring
      _ ≤ (t ^ (σ₀ - 2 * δ) + t ^ (σ₀ + 2 * δ)) / δ :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hδ.le

end

end GroundTheory.Global
