import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.HaarSum
open MeasureTheory

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) :
    μ.real H' * (H'.relIndex H : ℝ) = μ.real H ∧ H'.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

theorem integral_eq_sum_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Subgroup G) (hS : IsOpen (S : Set G))
    (hfin : μ (S : Set G) ≠ ⊤) (u : G → ℂ) (hu : ∀ x, ∀ s ∈ S, u (x * s) = u x) (F : Finset (G ⧸ S))
    (hF : ∀ q : G ⧸ S, q ∉ F → u q.out = 0) :
    ∫ x, u x ∂μ = (μ.real (S : Set G) : ℂ) * ∑ q ∈ F, u q.out := by
  have key : ∀ x : G, u ((x : G ⧸ S).out) = u x := fun x => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    rw [hh]
    exact hu x h h.2
  have hset : ∀ q : G ⧸ S, {x : G | (x : G ⧸ S) = q} = (fun x => q.out⁻¹ * x) ⁻¹' (S : Set G) := by
    intro q
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm]
    exact QuotientGroup.eq
  have hmeas : ∀ q : G ⧸ S, MeasurableSet {x : G | (x : G ⧸ S) = q} := fun q => by
    rw [hset]
    exact (hS.preimage (continuous_mul_left _)).measurableSet
  have hμ : ∀ q : G ⧸ S, μ {x : G | (x : G ⧸ S) = q} = μ (S : Set G) := fun q => by
    rw [hset]
    exact measure_preimage_mul μ _ _
  have hfun : u = fun x => ∑ q ∈ F, ({x : G | (x : G ⧸ S) = q}.indicator (fun _ => u q.out) x) := by
    funext x
    rw [Finset.sum_eq_single (x : G ⧸ S)]
    · simp [Set.indicator, key]
    · intro q _ hq
      simp [Set.indicator, Ne.symm hq]
    · intro hx
      have h0 := hF _ hx
      rw [key] at h0
      simp [Set.indicator, key, h0]
  conv_lhs => rw [hfun]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), Measure.real, hμ q, Complex.real_smul, Measure.real]
  · intro q _
    exact (integrableOn_const (hμ q ▸ hfin)).integrable_indicator (hmeas q)

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    (hS : IsOpen (S : Set G)) {C : Set G} (hC : IsCompact C) : ((fun x : G => (x : G ⧸ S)) '' C).Finite := by
  haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  exact (hC.image (continuous_coinduced_rng : Continuous fun x : G => (x : G ⧸ S))).finite_of_discrete

theorem hint_eq_integral : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ,
    (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u →
    GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) =
      ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  intro V _ _ _ μ hμ Λ hΛo hΛc u ⟨U, hUo, hU⟩ hsupp
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI := hμ
  let G := Multiplicative V
  letI : MeasurableSpace G := borel V
  haveI : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := μ
  haveI : ν.IsMulLeftInvariant := ⟨fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) (Multiplicative.toAdd g)⟩
  let u' : G → ℂ := fun X => u (Multiplicative.toAdd X)
  let K : Subgroup G := AddSubgroup.toSubgroup Λ
  let S : Subgroup G := rStab u' ⊓ K
  have hSK : S ≤ K := inf_le_right
  have hSo : IsOpen (S : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := AddSubgroup.toSubgroup (U ⊓ Λ)) ?_ ?_
    · intro x hx
      refine ⟨fun y => hU _ _ hx.1, hx.2⟩
    · exact hUo.inter hΛo
  have hKc : IsCompact (K : Set G) := hΛc
  obtain ⟨hvol, hidx⟩ := vol_mul_relIndex ν K S hSK hKc hSo
  have hKpos : 0 < μ (Λ : Set V) := hΛo.measure_pos μ ⟨0, Λ.zero_mem⟩
  have hKfin : μ (Λ : Set V) < ⊤ := hΛc.measure_lt_top
  have hSfin : ν (S : Set G) ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono hSK)
  have hfinC := finite_cosets S hSo (C := tsupport u') hsupp
  have hF : ∀ q : G ⧸ S, q ∉ hfinC.toFinset → u' q.out = 0 := by
    intro q hq
    by_contra h
    apply hq
    rw [Set.Finite.mem_toFinset]
    exact ⟨q.out, subset_tsupport _ h, QuotientGroup.out_eq' q⟩
  have hint_eq := integral_eq_sum_cosets ν S hSo hSfin u' (fun x s hs => hs.1 x) hfinC.toFinset hF
  have hsum : ∑ᶠ q : G ⧸ S, u' q.out = ∑ q ∈ hfinC.toFinset, u' q.out := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra h
    exact hq (hF q h)
  have hKr : (μ (Λ : Set V)).toReal = ν.real (S : Set G) * (S.relIndex K : ℝ) := hvol.symm
  have hKne : (μ (Λ : Set V)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKpos.ne', hKfin.ne⟩
  have hSne : ν.real (S : Set G) ≠ 0 := by
    intro h0
    rw [hKr, h0, zero_mul] at hKne
    exact hKne rfl
  change (((S.relIndex K : ℕ) : ℂ))⁻¹ * ∑ᶠ q : G ⧸ S, u' q.out = _ * ∫ x : G, u' x ∂ν
  rw [hint_eq, hsum, hKr]
  have hidx' : ((S.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hSne' : ((ν.real (S : Set G) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSne
  push_cast
  field_simp

end GlobalTheory.HaarSum
