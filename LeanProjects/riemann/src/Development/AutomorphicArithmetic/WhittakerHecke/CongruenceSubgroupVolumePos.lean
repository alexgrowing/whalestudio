import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem kappa_ne_zero (M : Meas ℚ)
    {U : Set (G1 ℚ)} (hU : IsOpen U) {k : G1 ℚ} (hk : k ∈ KK ℚ) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ
  have hmem : ∀ x ∈ KK ℚ, ∀ y ∈ KK ℚ, x * y⁻¹ ∈ KK ℚ := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).inv_mem hy)
  have hnull : ∀ c ∈ KK ℚ, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 ℚ => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK ℚ) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK ℚ) + M.κ (KK ℚ)ᶜ := by
    rw [← Set.union_compl_self (KK ℚ)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

private theorem cp_cont (v : H.P ℚ) : Continuous (H.cp v) := by
  have h1 : Continuous (pLoc ℚ v) :=
    RestrictedProduct.continuous_eval (R := fun v : H.P ℚ => v.adicCompletion ℚ) v
  have h2 : Continuous (pFin ℚ) := continuous_snd
  exact h1.comp h2

private theorem isOpen_dv {N : ℕ} (hN : 0 < N) (v : H.P ℚ) :
    IsOpen {k : G1 ℚ | Dv N v (k 1 0)} := by
  have hN0 : (N : H.Kv v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hv0 : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 hN0
  have hO : IsOpen ((v.adicCompletionIntegers ℚ : ValuationSubring (H.Kv v)) : Set (H.Kv v)) :=
    Valued.isOpen_valuationSubring _
  have hc : Continuous fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹ := by
    have hk : Continuous fun k : G1 ℚ => (k.1 : Matrix (Fin 2) (Fin 2) (A ℚ)) 1 0 :=
      (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_elem 1 0
    exact ((cp_cont v).comp hk).mul continuous_const
  have : {k : G1 ℚ | Dv N v (k 1 0)} =
      (fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ⁻¹' ((v.adicCompletionIntegers ℚ : ValuationSubring (H.Kv v)) : Set (H.Kv v)) := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Dv]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    rw [← div_eq_mul_inv]
    exact (div_le_one₀ (zero_lt_iff.2 hv0)).symm
  rw [this]
  exact hO.preimage hc

private theorem val_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) :
    Valued.v (n : H.Kv v) = v.valuation K (n : K) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (n : K)]
  congr 1
  exact (map_natCast (algebraMap K (H.Kv v)) n).symm

private theorem dv_of_int {N : ℕ} (hN : 0 < N) (v : H.P ℚ)
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 ℚ) ((N : ℚ)⁻¹)) {x : A ℚ}
    (hx : Valued.v (H.cp v x) ≤ 1) : Dv N v x := by
  have h1 : ¬ 1 < v.valuation ℚ ((N : ℚ)⁻¹) := hv
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : (1 : _) ≤ v.valuation ℚ (N : ℚ) := by
    rw [map_inv₀] at h1
    have h3 := not_lt.1 h1
    have hp : 0 < v.valuation ℚ (N : ℚ) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
    exact (inv_le_one₀ hp).1 h3
  have h4 : Valued.v (N : H.Kv v) = v.valuation ℚ (N : ℚ) := val_nat v N
  refine hx.trans ?_
  rw [h4]
  exact h2

theorem UpperTheory.congruenceSubgroup_volume_pos :
    ∀ (M : Meas ℚ) (N : ℕ), 0 < N → 0 < cK M N := by
  intro M N hN
  haveI := M.prob
  have hfin := HeightOneSpectrum.Support.finite (𝓞 ℚ) ((N : ℚ)⁻¹)
  set T := HeightOneSpectrum.Support (𝓞 ℚ) ((N : ℚ)⁻¹) with hT
  set U : Set (G1 ℚ) := ⋂ v ∈ T, {k : G1 ℚ | Dv N v (k 1 0)} with hU
  have hUo : IsOpen U := hfin.isOpen_biInter fun v _ => isOpen_dv hN v
  have h1K : (1 : G1 ℚ) ∈ KK ℚ := by
    rw [(UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).1]
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).one_mem
  have h1U : (1 : G1 ℚ) ∈ U := by
    refine Set.mem_iInter₂.2 fun v _ => ?_
    simp [Dv]
  have hne := kappa_ne_zero M hUo h1K h1U
  refine ENNReal.toReal_pos (fun h0 => hne ?_) (measure_ne_top _ _)
  refine measure_mono_null (t := (SS N ∩ KK ℚ) ∪ (KK ℚ)ᶜ) ?_ (measure_union_null h0 M.supp)
  intro k hk
  by_cases hkK : k ∈ KK ℚ
  · refine Or.inl ⟨fun v => ?_, hkK⟩
    by_cases hv : v ∈ T
    · exact Set.mem_iInter₂.1 hk v hv
    · refine dv_of_int hN v hv ?_
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hkK.2 v 1 0)
  · exact Or.inr hkK
