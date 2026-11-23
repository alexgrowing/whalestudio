import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_mono' {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem majorant {F : Type} [Field F] [NumberField F] {G : V4 F → ℂ}
    (hG : G ∈ schwartzBruhatPi F (Fin 4)) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖G v‖ ≤ B * wt K N v := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hgc : Continuous g := ((mem_finiteSchwartzBruhatPi F).mp hg).1.continuous
    have hgs : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi F).mp hg).2
    obtain ⟨C₂, h₂⟩ := hgc.bounded_above_of_compact_support hgs
    refine ⟨tsupport g, hgs.isCompact, fun N => ?_⟩
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_inv_one_add_pow φ N
    refine ⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), fun v => ?_⟩
    simp only [schwartzBruhatTensorPi, norm_mul]
    by_cases hx : finPartPi v ∈ tsupport g
    · rw [wt, if_pos hx]
      calc ‖φ (infPartPi v)‖ * ‖g (finPartPi v)‖
          ≤ (C₁ * ((1 + ‖infPartPi v‖) ^ N)⁻¹) * max C₂ 0 :=
            mul_le_mul (h₁ _) ((h₂ _).trans (le_max_left _ _)) (norm_nonneg _)
              (mul_nonneg hC₁ (inv_nonneg.2 (by positivity)))
        _ = C₁ * max C₂ 0 * ((1 + ‖infPartPi v‖) ^ N)⁻¹ := by ring
    · rw [wt, if_neg hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  | zero =>
    exact ⟨∅, isCompact_empty, fun N => ⟨0, le_rfl, fun v => by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, hK₁, h₁⟩ := hG
    obtain ⟨K₂, hK₂, h₂⟩ := hH
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun N => ?_⟩
    obtain ⟨B₁, hB₁, b₁⟩ := h₁ N
    obtain ⟨B₂, hB₂, b₂⟩ := h₂ N
    refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun v => ?_⟩
    calc ‖(G + H) v‖ ≤ ‖G v‖ + ‖H v‖ := norm_add_le _ _
      _ ≤ B₁ * wt K₁ N v + B₂ * wt K₂ N v := add_le_add (b₁ v) (b₂ v)
      _ ≤ B₁ * wt (K₁ ∪ K₂) N v + B₂ * wt (K₁ ∪ K₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_left N v) hB₁)
            (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_right N v) hB₂)
      _ = (B₁ + B₂) * wt (K₁ ∪ K₂) N v := by ring
  | smul c G _ hG =>
    obtain ⟨K, hK, h⟩ := hG
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB, b⟩ := h N
    refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b v) (norm_nonneg c)

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtBound :
    ∀ (F : Type) [Field F] [NumberField F], WtBound F := by
  intro F _ _ φ
  refine ⟨continuous_of_mem_schwartzBruhatPi φ.2, ?_⟩
  obtain ⟨K, hK, h⟩ := majorant φ.2
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨B, _, b⟩ := h N
  exact ⟨B, fun _ _ v => b v⟩
