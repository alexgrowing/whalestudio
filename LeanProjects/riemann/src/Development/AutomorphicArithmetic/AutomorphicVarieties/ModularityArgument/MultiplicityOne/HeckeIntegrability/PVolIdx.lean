import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

private theorem haar_measure_rel_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : MeasureTheory.Measure Γ) [μ.IsHaarMeasure]
    (K K' : Subgroup Γ) (hK' : IsOpen (K' : Set Γ)) (hK : IsCompact (K : Set Γ)) (hle : K' ≤ K) :
    (μ K').toReal * (K'.relIndex K : ℕ) = (μ K).toReal := by
  classical
  have hopen : ∀ g : Γ, IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K' : Set Γ)) := fun g =>
    hK'.preimage (continuous_const.mul continuous_id)
  have hcov : (K : Set Γ) ⊆ ⋃ k : K, (fun x => (k : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    simp [K'.one_mem]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun k : K => hopen (k : Γ)) hcov
  have hmem : ∀ a b : K, ((a : Γ)⁻¹ * (b : Γ) ∈ K') ↔
      (QuotientGroup.mk a : K ⧸ K'.subgroupOf K) = QuotientGroup.mk b := by
    intro a b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hfin : Finite (K ⧸ K'.subgroupOf K) := by
    refine Finite.of_surjective
      (fun k : t => (QuotientGroup.mk (k : K) : K ⧸ K'.subgroupOf K)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (ht x.2)
      exact ⟨⟨k, hk⟩, (hmem k x).1 hx⟩
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let s : K ⧸ K'.subgroupOf K → K := Quotient.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ K'.subgroupOf K) = q := fun q =>
    QuotientGroup.out_eq' q
  let f : K ⧸ K'.subgroupOf K → Set Γ := fun q =>
    (fun x => ((s q : K) : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ)
  have hU : (K : Set Γ) = ⋃ q, f q := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      exact (hmem _ ⟨x, hx⟩).2 (hs _)
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
      have h1 : ((s q : K) : Γ)⁻¹ * x ∈ K := hle hq
      have h2 := K.mul_mem (s q).2 h1
      simpa using h2
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro p q hpq
    refine Set.disjoint_left.2 ?_
    intro x hp hq
    apply hpq
    have hp' : ((s p : K) : Γ)⁻¹ * x ∈ K' := hp
    have hq' : ((s q : K) : Γ)⁻¹ * x ∈ K' := hq
    have h3 : ((s p : K) : Γ)⁻¹ * (s q : K) ∈ K' := by
      have := K'.mul_mem hp' (K'.inv_mem hq')
      simpa [mul_assoc] using this
    rw [← hs p, ← hs q]
    exact (hmem _ _).1 h3
  have hμ : ∀ q, μ (f q) = μ K' := fun q =>
    MeasureTheory.measure_preimage_mul μ _ _
  have hsum := MeasureTheory.measure_iUnion (μ := μ) hdisj (fun q => (hopen _).measurableSet)
  rw [← hU, tsum_fintype] at hsum
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]
  simp only [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem UpperTheory.V.Z.Mult.Pi.volIdx_pf :
    VolIdx := by
  intro Γ _ _ _ _ _ μ _ K K' hK' hK hle
  exact haar_measure_rel_index μ K K' hK' hK hle
