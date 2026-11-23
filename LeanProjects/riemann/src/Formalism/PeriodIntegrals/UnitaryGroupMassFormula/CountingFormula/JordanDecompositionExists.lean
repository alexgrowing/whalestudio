import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NormMMOfJD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists

open NumberField Module

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Bridge

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem nondegOn_of_gram (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) (hdet : (gram h x).det ≠ 0) :
    Formalism.L2.SG.Pf.Cnt.NondegOn h (Submodule.span K (Set.range x)) := by
  intro v hv hv0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hvec : Matrix.vecMul (fun i => star (c i)) (gram h x) = 0 := by
    funext j
    have := hv0 (x j) (Submodule.subset_span ⟨j, rfl⟩)
    simpa [gram, Matrix.vecMul, dotProduct, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply] using this
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  have hc : c = 0 := by
    funext i
    have := congrFun h0 i
    simpa using this
  simp [hc]

theorem isLatIn_pb (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hne : ∀ i, 𝔞 i ≠ 0) :
    Formalism.L2.SG.Pf.Cnt.IsLatIn (Submodule.span K (Set.range x)) (pbLat x 𝔞) := by
  refine ⟨?_, ?_⟩
  ·
    have hden : ∀ i, ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ c ∈ 𝔞 i, ∃ o : 𝓞 K, (o : K) = (d : K) * c := by
      intro i
      obtain ⟨d, hd, hdi⟩ := (𝔞 i).isFractional
      refine ⟨d, nonZeroDivisors.ne_zero hd, fun c hc => ?_⟩
      obtain ⟨o, ho⟩ := hdi c hc
      exact ⟨o, by rw [← Algebra.smul_def]; exact ho⟩
    choose d hd0 hd using hden
    set N : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range fun i => ((d i : K))⁻¹ • x i)
    have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
    have hle : pbLat x 𝔞 ≤ N := by
      refine Submodule.span_le.mpr ?_
      rintro v ⟨i, c, hc, rfl⟩
      obtain ⟨o, ho⟩ := hd i c hc
      have hdi : ((d i : K)) ≠ 0 := by exact_mod_cast hd0 i
      have : c • x i = o • (((d i : K))⁻¹ • x i) := by
        rw [← algebraMap_smul K o, smul_smul]
        show c • x i = ((o : K) * ((d i : K))⁻¹) • x i
        rw [ho, mul_comm (d i : K), mul_assoc, mul_inv_cancel₀ hdi, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    haveI : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hNfg
    have hfg := IsNoetherian.noetherian ((pbLat x 𝔞).comap N.subtype)
    have hmap := hfg.map N.subtype
    rwa [Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact hle)] at hmap
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      have hle' : pbLat x 𝔞 ≤ (Submodule.span K (Set.range x)).restrictScalars (𝓞 K) := by
        refine Submodule.span_le.mpr ?_
        rintro w ⟨i, c, hc, rfl⟩
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
      exact hle' hv
    · rw [Submodule.span_le]
      rintro v ⟨i, rfl⟩
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (fun hb => hne i (FractionalIdeal.coeToSubmodule_eq_bot.mp hb))
      have hm : c • x i ∈ pbLat x 𝔞 := Submodule.subset_span ⟨i, c, hc, rfl⟩
      have : x i = c⁻¹ • (c • x i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

end Bridge

theorem jordan_decomposition_exists : JordanExists := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hcm hfix _ hsymm _ hne _ hspan hdet hint 𝔭 h𝔭
  subst hspan
  exact (Formalism.L2.SG.Pf.Cnt.jordan_splitting_exists K F V hcm hfix h hsymm).1 _ _ (nondegOn_of_gram h x hdet)
    (isLatIn_pb x 𝔞 hne) hint 𝔭 h𝔭

theorem norm_mass_of_jordan : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_J jordan_decomposition_exists

end PI.UnitaryGroupMassFormula.CntFormula.R6
