import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical nonZeroDivisors

namespace GlobalTheory.CompanionTheory.EpsteinTensorBound

open Ad3.R GroundTheory.Automorphic.Adele2 IdeleGroup

theorem lrow_apply (z : Jd) (κ : G2) (j : Fin 2) :
    lrow z κ j = (z : 𝔸[ℚ]) * (κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j := by
  simp [lrow, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem abs_realEquiv (x : InfiniteAdeleRing ℚ) :
    |RationalIdeles.realEquiv x| = ‖x default‖ := by
  rw [RationalIdeles.realEquiv_apply, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (RationalIdeles.isReal_infinitePlace default)).norm_map_of_map_zero (map_zero _) _

theorem exists_half_le_row {κ : G2} (hκ : κ ∈ (maxCompact : Subgroup G2)) :
    ∃ j : Fin 2, 1 / 2 ≤ ‖((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default‖ := by
  have h := (GroundTheory.Automorphic.GL2Classical.realPart_orthogonal hκ).2.1
  have hE : ∀ j : Fin 2, ‖((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default‖ =
      |(realPart κ : Matrix (Fin 2) (Fin 2) ℝ) 1 j| := fun j ↦
    (abs_realEquiv _).symm
  by_contra hc
  push Not at hc
  have h0 := hc 0
  have h1 := hc 1
  rw [hE] at h0 h1
  have a0 := abs_lt.1 h0
  have a1 := abs_lt.1 h1
  nlinarith

theorem norm_le_two_mul_infPart (z : Jd) {κ : G2} (hκ : κ ∈ (maxCompact : Subgroup G2)) :
    ‖((toInfinite ℚ z : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) default‖ ≤
      2 * ‖Adele2.infPart (lrow z κ)‖ := by
  obtain ⟨j, hj⟩ := exists_half_le_row hκ
  have h1 : ‖(lrow z κ j).1 default‖ ≤ ‖Adele2.infPart (lrow z κ)‖ :=
    (norm_le_norm_homeomorphMixedSpace _ _).trans (norm_le_pi_norm (Adele2.infPart (lrow z κ)) j)
  have h2 : (lrow z κ j).1 default = (z : 𝔸[ℚ]).1 default *
      ((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default := by
    rw [lrow_apply]; rfl
  rw [h2, norm_mul] at h1
  have h3 : ‖(z : 𝔸[ℚ]).1 default‖ * (1 / 2) ≤ ‖(z : 𝔸[ℚ]).1 default‖ *
      ‖((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default‖ :=
    mul_le_mul_of_nonneg_left hj (norm_nonneg _)
  change ‖(z : 𝔸[ℚ]).1 default‖ ≤ _
  linarith

theorem exists_norm_schwartz_lrow_le (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Jd) (κ : G2), κ ∈ (maxCompact : Subgroup G2) →
      ‖φ (Adele2.infPart (lrow z κ))‖ ≤ C * ∏ w : InfinitePlace ℚ,
        ((1 + ‖((toInfinite ℚ z : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) w‖) ^ k)⁻¹ := by
  set S := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨2 ^ k * S, by positivity, fun z κ hκ ↦ ?_⟩
  set y := Adele2.infPart (lrow z κ)
  set a := ‖((toInfinite ℚ z : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) default‖ with ha
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl φ y
  rw [norm_iteratedFDeriv_zero] at h1
  have h2 : a ≤ 2 * ‖y‖ := norm_le_two_mul_infPart z hκ
  have ha0 : 0 ≤ a := norm_nonneg _
  have h3 : (1 + a) ^ k ≤ 2 ^ k * (1 + ‖y‖) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  rw [Fintype.prod_unique, ← div_eq_mul_inv]
  have hpos : 0 < (1 + a) ^ k := by positivity
  change ‖φ y‖ ≤ 2 ^ k * S / (1 + a) ^ k
  rw [le_div_iff₀ hpos]
  calc ‖φ y‖ * (1 + a) ^ k ≤ ‖φ y‖ * (2 ^ k * (1 + ‖y‖) ^ k) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = 2 ^ k * ((1 + ‖y‖) ^ k * ‖φ y‖) := by ring
    _ ≤ 2 ^ k * S := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem mul_mem_idealFiniteAdeles {L : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ} {x u : Af}
    (hx : x ∈ idealFiniteAdeles L) (hu : u ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    x * u ∈ idealFiniteAdeles L := by
  rw [mem_idealFiniteAdeles] at hx ⊢
  intro v
  have h1 : Valued.v (u v) ≤ 1 := hu v
  calc Valued.v ((x * u) v) = Valued.v (x v) * Valued.v (u v) := map_mul _ _ _
    _ ≤ _ * 1 := mul_le_mul' (hx v) h1
    _ = _ := mul_one _

theorem mem_ideal_of_row {L : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ} (z : Jd) {κ : G2}
    (hκ : κ ∈ (maxCompact : Subgroup G2))
    (h : ∀ j, Adele2.finPart (lrow z κ) j ∈ idealFiniteAdeles L) :
    (z : 𝔸[ℚ]).2 ∈ idealFiniteAdeles L := by
  set P := (AdelicGLn.prodEquiv ℚ 2 κ).2 with hP
  obtain ⟨-, hQ⟩ := (AdelicGLn.mem_integralFiniteGL_iff ℚ 2).1
    (GroundTheory.Automorphic.GL2Classical.finitePart_mem_integralFiniteGL hκ)
  have hPQ : (P : Matrix (Fin 2) (Fin 2) Af) * ((P⁻¹ : GL (Fin 2) Af) : Matrix (Fin 2) (Fin 2) Af) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h11 := congrFun (congrFun hPQ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h11
  have hrow : ∀ j, Adele2.finPart (lrow z κ) j = (z : 𝔸[ℚ]).2 * (P : Matrix (Fin 2) (Fin 2) Af) 1 j := by
    intro j
    change (lrow z κ j).2 = _
    rw [lrow_apply]
    rfl
  have key : (z : 𝔸[ℚ]).2 =
      Adele2.finPart (lrow z κ) 0 * ((P⁻¹ : GL (Fin 2) Af) : Matrix (Fin 2) (Fin 2) Af) 0 1 +
      Adele2.finPart (lrow z κ) 1 * ((P⁻¹ : GL (Fin 2) Af) : Matrix (Fin 2) (Fin 2) Af) 1 1 := by
    rw [hrow, hrow]
    linear_combination (-(z : 𝔸[ℚ]).2) * h11
  rw [key]
  exact add_mem (mul_mem_idealFiniteAdeles (h 0) (hQ 0 1)) (mul_mem_idealFiniteAdeles (h 1) (hQ 1 1))

theorem continuous_tensor (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) {g : (Fin 2 → Af) → ℂ}
    (hg : g ∈ finiteSchwartzBruhat2 ℚ) : Continuous (schwartzBruhatTensor2 φ g) := by
  have h1 : Continuous (Adele2.infPart (K := ℚ)) :=
    continuous_pi fun i ↦ (homeomorphMixedSpace ℚ).continuous.comp
      (continuous_fst.comp (continuous_apply i))
  have h2 : Continuous (Adele2.finPart (K := ℚ)) :=
    continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i)
  exact (φ.continuous.comp h1).mul (hg.1.continuous.comp h2)

theorem continuous_of_mem {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 ℚ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact continuous_tensor φ hg
  | zero => exact continuous_const
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

theorem exists_bound_tensor (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) {g : (Fin 2 → Af) → ℂ}
    (hg : g ∈ finiteSchwartzBruhat2 ℚ) (τ : ℝ) :
    ∃ C : ℝ, ∃ k : ℕ, ∃ L : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ, 0 ≤ C ∧ 2 * τ + 2 < k ∧
      ∀ (z : Jd) (κ : G2), κ ∈ (maxCompact : Subgroup G2) →
        ‖schwartzBruhatTensor2 φ g (lrow z κ)‖ * md z ^ τ ≤
          C * (infiniteZetaBound τ k (toInfinite ℚ z) * finiteZetaBound L τ (toFinite ℚ z)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * τ + 2 < k := exists_nat_gt _
  obtain ⟨C₁, hC₁, hφ⟩ := exists_norm_schwartz_lrow_le φ k
  obtain ⟨M, hM⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hcpt : IsCompact (tsupport g) := hg.2
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles
    ((hcpt.image (continuous_apply (0 : Fin 2))).union (hcpt.image (continuous_apply (1 : Fin 2))))
  refine ⟨C₁ * max M 0, k, L, by positivity, hk, fun z κ hκ ↦ ?_⟩
  set a := toInfinite ℚ z
  set b := toFinite ℚ z
  have hinf : ‖φ (Adele2.infPart (lrow z κ))‖ *
      ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ) ≤ C₁ * infiniteZetaBound τ k a := by
    calc ‖φ (Adele2.infPart (lrow z κ))‖ * ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ)
        ≤ (C₁ * ∏ w, ((1 + ‖(a : InfiniteAdeleRing ℚ) w‖) ^ k)⁻¹) *
            ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ) :=
          mul_le_mul_of_nonneg_right (hφ z κ hκ) (Finset.prod_nonneg fun w _ ↦ by positivity)
      _ = C₁ * infiniteZetaBound τ k a := by
          rw [mul_assoc, ← Finset.prod_mul_distrib, infiniteZetaBound]
          congr 1
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          rw [div_eq_mul_inv, mul_comm]
  have hI := infiniteZetaBound_nonneg τ k a
  unfold schwartzBruhatTensor2
  by_cases hb : (b : Af) ∈ idealFiniteAdeles L
  · have hfz : finiteZetaBound L τ b = finiteModule (ofFinite b) ^ τ := by
      rw [finiteZetaBound, if_pos hb]
    rw [hfz, md, ideleModule_rpow_eq, norm_mul]
    have hgM : ‖g (Adele2.finPart (lrow z κ))‖ ≤ max M 0 := (hM _).trans (le_max_left _ _)
    have hfm : 0 ≤ finiteModule (ofFinite b) ^ τ := by
      have := finiteModule_pos (ofFinite b)
      positivity
    calc ‖φ (Adele2.infPart (lrow z κ))‖ * ‖g (Adele2.finPart (lrow z κ))‖ *
          ((∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ)) *
            finiteModule (ofFinite b) ^ τ)
        = (‖φ (Adele2.infPart (lrow z κ))‖ *
            ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ)) *
              ‖g (Adele2.finPart (lrow z κ))‖ * finiteModule (ofFinite b) ^ τ := by ring
      _ ≤ (C₁ * infiniteZetaBound τ k a) * max M 0 * finiteModule (ofFinite b) ^ τ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hinf hgM (norm_nonneg _) (mul_nonneg hC₁ hI)) hfm
      _ = C₁ * max M 0 * (infiniteZetaBound τ k a * finiteModule (ofFinite b) ^ τ) := by ring
  · have hg0 : g (Adele2.finPart (lrow z κ)) = 0 := by
      by_contra h
      have hs := subset_tsupport g h
      refine hb (mem_ideal_of_row z hκ fun j ↦ ?_)
      fin_cases j
      · exact hL (Or.inl ⟨_, hs, rfl⟩)
      · exact hL (Or.inr ⟨_, hs, rfl⟩)
    rw [hg0, mul_zero, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (mul_nonneg hI (finiteZetaBound_nonneg _ _ _))

theorem exists_dominant {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 ℚ) {τ : ℝ} (hτ : 1 < τ) :
    ∃ B : Jd → ℝ, Integrable B (ideleMeasure ℚ) ∧ ∀ (z : Jd) (κ : G2),
      κ ∈ (maxCompact : Subgroup G2) → ‖Φ (lrow z κ)‖ * md z ^ τ ≤ B z := by
  have hpow : ∀ z : Jd, 0 ≤ md z ^ τ := fun z ↦ Real.rpow_nonneg (ideleModule ℚ z).2.le τ
  induction hΦ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨C, k, L, -, hk, hb⟩ := exists_bound_tensor φ hg τ
    exact ⟨_, (integrable_zetaBound hτ hk L).const_mul C, hb⟩
  | zero =>
    refine ⟨0, integrable_zero _ _ _, fun z κ _ ↦ ?_⟩
    simp
  | add G H _ _ hG hH =>
    obtain ⟨B₁, h₁, b₁⟩ := hG
    obtain ⟨B₂, h₂, b₂⟩ := hH
    refine ⟨B₁ + B₂, h₁.add h₂, fun z κ hκ ↦ ?_⟩
    calc ‖(G + H) (lrow z κ)‖ * md z ^ τ ≤ (‖G (lrow z κ)‖ + ‖H (lrow z κ)‖) * md z ^ τ :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (hpow z)
      _ ≤ B₁ z + B₂ z := by
          rw [add_mul]
          exact add_le_add (b₁ z κ hκ) (b₂ z κ hκ)
  | smul c G _ hG =>
    obtain ⟨B, h, b⟩ := hG
    refine ⟨fun z ↦ ‖c‖ * B z, h.const_mul _, fun z κ hκ ↦ ?_⟩
    simp only [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b z κ hκ) (norm_nonneg _)

theorem g3a : Ad3.R.G3a := by
  intro Φ hΦ
  refine ⟨continuous_of_mem hΦ, fun τ hτ ↦ ?_⟩
  obtain ⟨B, hB, hle⟩ := exists_dominant hΦ hτ
  refine ⟨∫⁻ z, ENNReal.ofReal (B z) ∂ideleMeasure ℚ, hB.lintegral_lt_top, fun κ ↦
    lintegral_mono fun z ↦ ?_⟩
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hle z κ.1 κ.2)

end GlobalTheory.CompanionTheory.EpsteinTensorBound
