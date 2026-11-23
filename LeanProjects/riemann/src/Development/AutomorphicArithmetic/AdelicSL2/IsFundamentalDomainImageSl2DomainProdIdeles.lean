import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
import Development.AutomorphicArithmetic.AdelicSL2.ExistsGl2RatSmulMemRangeAdelicSL2IdeleMap
import Development.AutomorphicArithmetic.AdelicSL2.EqSl2RatMulOfGl2RatSmulAdelicSL2IdeleMapEq
import Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeSl2IdeleMapEqSmulProd
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Pointwise Classical ENNReal NNReal

theorem UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles :
    ∀ (M : Meas ℚ) (U : UMeas) (μ : Measure GG) [μ.IsHaarMeasure], IsFundamentalDomain Ga (pm '' (M.D ×ˢ Set.univ)) μ := by
  intro M U μ _
  haveI := M.haar
  have emb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have null : ∀ N : Set (G1 ℚ), M.μ N = 0 → μ (pm '' (N ×ˢ Set.univ)) = 0 := fun N hN => by
    rw [← Measure.restrict_eq_self μ (Set.image_subset_range _ _), hc, Measure.smul_apply, emb.map_apply,
      Set.preimage_image_eq _ emb.injective, Measure.prod_prod, hN, zero_mul, smul_zero]
  have lift : ∀ s : SpecialLinearGroup (Fin 2) ℚ, ∃ γ : Ga, ∀ p : G1 ℚ × US, γ • pm p = pm (ratS ℚ s * p.1, p.2) := fun s => by
    refine ⟨⟨pm (ratS ℚ s, 1), ?_⟩, fun p => Subtype.ext ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ⟨SpecialLinearGroup.toGL s, Units.ext ?_⟩
      change _ = (ratS ℚ s).1 * !![1, 0; 0, (1 : A ℚ)]
      rw [← Matrix.one_fin_two, mul_one]
      rfl
    · change gl (ratS ℚ s) * dM 1 * (gl p.1 * dM p.2.1) = gl (ratS ℚ s * p.1) * dM p.2.1
      have : dM (1 : (A ℚ)ˣ) = 1 := Units.ext Matrix.one_fin_two.symm
      rw [this, mul_one, ← mul_assoc, ← map_mul]
  refine ⟨(emb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)).nullMeasurableSet, ?_, fun γ γ' hne => ?_⟩
  · have h0 := null _ (ae_iff.1 M.fund.ae_covers)
    rw [ae_iff]
    refine measure_mono_null (t := ⋃ γ : Ga, (fun x : GG => (γ : GG) * x) ⁻¹'
      (pm '' ({g | ¬ ∃ s : Gam ℚ, s • g ∈ M.D} ×ˢ Set.univ))) (fun x hx => ?_)
      (measure_iUnion_null fun γ => by rw [measure_preimage_mul]; exact h0)
    obtain ⟨γ, p, hp⟩ := UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap x
    refine Set.mem_iUnion.2 ⟨γ, p, ⟨?_, trivial⟩, hp⟩
    rintro ⟨⟨_, s, rfl⟩, hs⟩
    obtain ⟨δ, hδ⟩ := lift s
    exact hx ⟨δ * γ, (ratS ℚ s * p.1, p.2), ⟨hs, trivial⟩, by rw [mul_smul, ← hp, hδ]⟩
  · haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
    haveI : Countable (SpecialLinearGroup (Fin 2) ℚ) := Subtype.countable
    have hN : M.μ (⋃ s : {s : SpecialLinearGroup (Fin 2) ℚ // ratS ℚ s ≠ 1},
        ((⟨ratS ℚ s.1, s.1, rfl⟩ : Gam ℚ) • M.D ∩ (1 : Gam ℚ) • M.D)) = 0 :=
      measure_iUnion_null fun s => M.fund.aedisjoint fun h => s.2 (congrArg Subtype.val h)
    refine measure_mono_null (t := (fun x : GG => ((γ'⁻¹ : Ga) : GG) * x) ⁻¹' (pm '' (_ ×ˢ Set.univ))) ?_
      (by rw [measure_preimage_mul]; exact null _ hN)
    rintro x ⟨⟨_, ⟨p, hp, rfl⟩, e⟩, ⟨_, ⟨q, hq, rfl⟩, e'⟩⟩
    have e1 : (γ'⁻¹ * γ) • pm p = pm q := by
      rw [mul_smul, inv_smul_eq_iff]
      exact e.trans e'.symm
    obtain ⟨-, s, h1, h2⟩ := UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq _ p q e1
    have hs : ratS ℚ s ≠ 1 := fun h => hne (by
      rw [h] at h2
      exact (inv_mul_eq_one.1 (Subtype.ext (Subtype.ext (h2.trans (Units.ext rfl))))).symm)
    refine ⟨q, ⟨Set.mem_iUnion.2 ⟨⟨s, hs⟩, ⟨p.1, hp.1, h1.symm⟩, by rw [one_smul]; exact hq.1⟩, trivial⟩, ?_⟩
    change pm q = γ'⁻¹ • x
    rw [eq_inv_smul_iff]
    exact e'
