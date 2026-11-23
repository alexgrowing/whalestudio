import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT PositivityTheory.Rg.BcB
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem coset_integral (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ K, h (g * k) = h g) :
    ∃ T : Finset (G ⧸ K), (∀ q : G ⧸ K, h q.out ≠ 0 → q ∈ T) ∧ ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ q ∈ T, (μ.real (K : Set G) : ℂ) * (h q.out * f q.out) := by
  let c : G ⧸ K → Set G := fun q => {y | q.out⁻¹ * y ∈ K}
  have hcm : ∀ q y, y ∈ c q ↔ (QuotientGroup.mk y : G ⧸ K) = q := by
    intro q y
    change q.out⁻¹ * y ∈ K ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hco : ∀ q, IsOpen (c q) := fun q => hK.preimage (continuous_const.mul continuous_id)
  have hmeas : ∀ q, μ (c q) = μ (K : Set G) := fun q => measure_preimage_mul μ q.out⁻¹ (K : Set G)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun g => c (QuotientGroup.mk g))
    (fun g _ => (hco _).mem_nhds ((hcm _ g).2 rfl))
  let T : Finset (G ⧸ K) := t.image fun g => (QuotientGroup.mk g : G ⧸ K)
  have hT : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ K) ∈ T := by
    intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport h hy))
    rw [(hcm _ y).1 hyg]
    exact Finset.mem_image_of_mem _ hg
  refine ⟨T, fun q hq => ?_, fun f hf => ?_⟩
  · simpa [QuotientGroup.out_eq'] using hT _ hq
  have hval : ∀ q y, y ∈ c q → h y * f y = h q.out * f q.out := by
    intro q y hy
    have e : y = q.out * (q.out⁻¹ * y) := by group
    rw [e, hinv _ _ hy, hf _ _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ q ∈ T, (c q).indicator (fun _ => h q.out * f q.out) y := by
    funext y
    by_cases hy : (QuotientGroup.mk y : G ⧸ K) ∈ T
    · have hyc : y ∈ c (QuotientGroup.mk y) := (hcm _ y).2 rfl
      rw [Finset.sum_eq_single (QuotientGroup.mk y : G ⧸ K), Set.indicator_of_mem hyc, hval _ y hyc]
      · intro q _ hq
        exact Set.indicator_of_notMem (fun hyq => hq ((hcm q y).1 hyq).symm) _
      · exact fun h' => (h' hy).elim
    · have hy0 : h y = 0 := by
        by_contra h'
        exact hy (hT y h')
      rw [hy0, zero_mul]
      refine (Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hyq => hy ?_) _).symm
      rwa [(hcm q y).1 hyq]
  rw [hsum, integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hco q).measurableSet]
    simp only [Measure.real, hmeas q, Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (hco q).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas q]; exact hfin)

end Abs

theorem heckeSum_pf : HeckeSum := by
  intro E _ _ _ n K hKo hKc μf _ h hh y hy
  have hfix : ∀ k ∈ K, finRep E n k y = y := fun k hk => by
    simpa using hy ⟨k, hk⟩
  obtain ⟨T, hT, hI⟩ := coset_integral μf hKo hKc.measure_lt_top.ne hh.1 (fun g k hk => (hh.2 k hk g).2)
  funext x
  have hf := hI (fun g => y.1 (x * finGL E n g)) (fun g k hk => by
    have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hfix k hk)
    have e' : y.1 (x * finGL E n g * finGL E n k) = y.1 (x * finGL E n g) := e
    simpa [mul_assoc] using e')
  have hL : Lv (finRep E n) K h = ∑ q ∈ T, h q.out • finRep E n q.out := by
    have hs : (Function.support fun q : GF E n ⧸ K => h q.out • (finRep E n q.out ∘ₗ LinearMap.id)) ⊆ T := by
      intro q hq
      refine hT q fun h0 => hq ?_
      simp [h0]
    simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rfl
  have hv : (∑ q ∈ T, (h q.out • finRep E n q.out) y : Sm E n).1 x =
      ∑ q ∈ T, h q.out * y.1 (x * finGL E n q.out) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hL, heckeOp, hf, LinearMap.sum_apply, hv, Finset.mul_sum]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
