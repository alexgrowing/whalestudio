import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL GroundTheory.Automorphic
open scoped ENNReal Pointwise

namespace PositivityTheory.KB.MomentRationality.Assem

section General

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_le_of_cover (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    {F T : Set G} (hF : IsFundamentalDomain Γ F μ) (f : G → ℝ≥0∞) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hT : ∀ x ∈ F, ∃ γ ∈ Γ, γ * x ∈ T) : ∫⁻ x in F, f x ∂μ ≤ ∫⁻ x in T, f x ∂μ := by
  have hcov : F ⊆ ⋃ g : Γ, g • T ∩ F := by
    intro x hx
    obtain ⟨γ, hγ, hxT⟩ := hT x hx
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hxT
  calc ∫⁻ x in F, f x ∂μ ≤ ∫⁻ x in ⋃ g : Γ, g • T ∩ F, f x ∂μ := lintegral_mono_set hcov
    _ ≤ ∑' g : Γ, ∫⁻ x in g • T ∩ F, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∫⁻ x in T, f x ∂μ := by
      rw [hF.setLIntegral_eq_tsum' f T]
      refine tsum_congr fun g => lintegral_congr fun x => ?_
      rw [Subgroup.smul_def]
      exact (hf _ (g⁻¹).2 x).symm

theorem setLIntegral_preimage_mul_left (μ : Measure G) [μ.IsMulLeftInvariant] (c : G) (S : Set G)
    (f : G → ℝ≥0∞) : ∫⁻ x in (fun x => c⁻¹ * x) ⁻¹' S, f x ∂μ = ∫⁻ y in S, f (c * y) ∂μ := by
  have key := (measurePreserving_mul_left μ c).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft c) f ((fun x => c⁻¹ * x) ⁻¹' S)
  simpa [Set.preimage_preimage] using key.symm

end General

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

omit [NumberField L] in
theorem continuous_ofS : Continuous (ofS L N) := by
  refine continuous_pi fun w => ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun x : Sp L N => ((x w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
    exact continuous_subtype_val.comp (continuous_apply w)
  · change Continuous fun x : Sp L N => (((x w)⁻¹ : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
    exact continuous_subtype_val.comp ((continuous_apply w).inv)

omit [NumberField L] in
theorem ofS_latS_mul {γ : Sp L N} (hγ : γ ∈ latS L N) (x : Sp L N) :
    ∃ δ : Gm L N, ofS L N (γ * x) = emb L N δ * ofS L N x := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨Matrix.SpecialLinearGroup.toGL g, ?_⟩
  rw [map_mul]
  congr 1
  funext w
  ext i j
  rfl

end PositivityTheory.KB.MomentRationality.Assem

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Assem

theorem sMom_of_parts (hD : SDisc) (hH : SHtB) (hI : SIntB) (hR : SRed) (h : SHt) : SMom := by
  intro L _ _ hL A
  refine ⟨A + 2, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hdisc, hcount⟩ := hD L N
  haveI := hdisc
  haveI := hcount
  obtain ⟨hcont, hinv, ⟨c0, hc0, hge⟩, -⟩ := h L hL N hN1
  obtain ⟨ι, hfin, c, M, T, hrat, hcov⟩ := hR L hL N hN1
  haveI := hfin
  let μ : Measure (Sp L N) := Measure.haar
  have hF : IsFundamentalDomain (latS L N)
      (GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N)) μ :=
    GroundTheory.Automorphic.RightCosetSpace.isFundamentalDomain_fundamentalDomain _ μ
  have hpos : ∀ x : Sp L N, 0 ≤ ht (ofS L N x) := fun x => le_trans hc0.le (hge _)
  have key : ∀ n : ℕ, n + 1 < N →
      ∫⁻ x in GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N),
        ENNReal.ofReal (ht (ofS L N x) ^ n) ∂μ < ∞ := by
    intro n hn
    let f : Sp L N → ℝ≥0∞ := fun x => ENNReal.ofReal (ht (ofS L N x) ^ n)
    have hfinv : ∀ γ ∈ latS L N, ∀ x, f (γ * x) = f x := by
      intro γ hγ x
      obtain ⟨δ, hδ⟩ := PositivityTheory.KB.MomentRationality.Assem.ofS_latS_mul hγ x
      simp only [f, hδ, hinv]
    have hcover : ∀ x ∈ GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N),
        ∃ γ ∈ latS L N, γ * x ∈ ⋃ j, (fun y => (c j)⁻¹ * y) ⁻¹' Sieg L N M T := by
      intro x _
      obtain ⟨γ, hγ, j, hj⟩ := hcov x
      exact ⟨γ, hγ, Set.mem_iUnion.2 ⟨j, hj⟩⟩
    refine lt_of_le_of_lt (PositivityTheory.KB.MomentRationality.Assem.lintegral_le_of_cover μ (latS L N) hF f hfinv hcover) ?_
    refine lt_of_le_of_lt (lintegral_iUnion_le _ _) ?_
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.2 fun j _ => ?_
    rw [PositivityTheory.KB.MomentRationality.Assem.setLIntegral_preimage_mul_left]
    obtain ⟨C, hC⟩ := hH L hL N hN1 (c j) (hrat j) M
    have hN2 : 2 ≤ N := by omega
    refine hI L hL N hN2 μ M T ((2 * n : ℕ) : ℝ) (by
        have : (n : ℝ) + 1 < N := by exact_mod_cast hn
        push_cast
        linarith) (ENNReal.ofReal (max C 0 ^ n)) ENNReal.ofReal_ne_top
      (fun y => f (c j * y)) ?_
    intro p hp s hs _ k hk
    have h1 : ht (ofS L N (c j * (p * dg L N s hs * k))) ≤ max C 0 * Real.exp (2 * W s) :=
      le_trans (hC p hp s hs k hk)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h2 : ht (ofS L N (c j * (p * dg L N s hs * k))) ^ n ≤
        max C 0 ^ n * Real.exp (((2 * n : ℕ) : ℝ) * W s) := by
      calc _ ≤ (max C 0 * Real.exp (2 * W s)) ^ n := pow_le_pow_left₀ (hpos _) h1 n
        _ = max C 0 ^ n * Real.exp (((2 * n : ℕ) : ℝ) * W s) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
    calc f (c j * (p * dg L N s hs * k))
        ≤ ENNReal.ofReal (max C 0 ^ n * Real.exp (((2 * n : ℕ) : ℝ) * W s)) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (max C 0 ^ n) * ENNReal.ofReal (Real.exp (((2 * n : ℕ) : ℝ) * W s)) :=
          ENNReal.ofReal_mul (pow_nonneg (le_max_right _ _) _)
  have hvol : μ (GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N)) < ∞ := by
    have := key 0 (by omega)
    simpa using this
  haveI : IsFiniteMeasure (GroundTheory.Automorphic.RightCosetSpace.quotientMeasure (latS L N) μ) := by
    refine ⟨?_⟩
    have h0 := GroundTheory.Automorphic.RightCosetSpace.lintegral_quotientMeasure (latS L N) μ (fun _ => 1)
    rw [lintegral_one, setLIntegral_one] at h0
    rw [h0]
    exact hvol
  have hright : μ.IsMulRightInvariant :=
    GroundTheory.Automorphic.RightCosetSpace.isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (latS L N) μ
  refine ⟨⟨μ, _, inferInstance, hright, hF, hvol⟩, ?_⟩
  refine ⟨((hcont.comp (PositivityTheory.KB.MomentRationality.Assem.continuous_ofS)).pow A).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => pow_nonneg (hpos x) A)]
  exact key A (by omega)

end PositivityTheory.KB

end
