import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_isFundamentalDomain_of_relIndex_ne_zero :
    ∀ (G X : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
      (μ : Measure X) [SMulInvariantMeasure G X μ] (Γ₀ Γ : Subgroup G) [Countable Γ] (s : Set X),
      Γ₀ ≤ Γ → Γ₀.relIndex Γ ≠ 0 → IsFundamentalDomain Γ s μ →
      ∃ t : Set X, IsFundamentalDomain Γ₀ t μ ∧ μ t = (Γ₀.relIndex Γ : ℝ≥0∞) * μ s := by
  intro G X _ _ _ _ μ _ Γ₀ Γ _ s hle hidx hs
  classical
  set H : Subgroup Γ := Γ₀.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hidx⟩
  let _ : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let ρ : Γ ⧸ H → Γ := fun q => q.out
  have hout : ∀ q : Γ ⧸ H, ((ρ q : Γ) : Γ ⧸ H) = q := fun q => QuotientGroup.out_eq' q
  have hρ : ∀ γ : Γ, (ρ (γ : Γ ⧸ H))⁻¹ * γ ∈ H := fun γ => QuotientGroup.eq.mp (hout _)
  let ι : Γ₀ → Γ := fun g => ⟨g, hle g.2⟩
  have key : ∀ (g : Γ₀) (γ : Γ), g • (γ • s) = (ι g * γ) • s := by
    intro g γ
    rw [mul_smul]
    rfl
  let t : Set X := ⋃ q : Γ ⧸ H, (ρ q)⁻¹ • s
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun q : Γ ⧸ H => (ρ q)⁻¹ • s) := by
    intro q q' hqq'
    apply hs.aedisjoint
    intro heq
    apply hqq'
    have h1 : ρ q = ρ q' := inv_injective heq
    rw [← hout q, ← hout q', h1]
  refine ⟨t, ⟨NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_smul _, ?_, ?_⟩, ?_⟩
  · filter_upwards [hs.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    refine ⟨⟨(((ρ (γ : Γ ⧸ H))⁻¹ * γ : Γ) : G), Subgroup.mem_subgroupOf.mp (hρ γ)⟩, ?_⟩
    refine Set.mem_iUnion.2 ⟨(γ : Γ ⧸ H), ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    convert hγ using 1
    simp [Subgroup.smul_def, smul_smul]
  · intro g g' hgg'
    show AEDisjoint μ (g • t) (g' • t)
    simp only [t, Set.smul_set_iUnion]
    rw [AEDisjoint.iUnion_left_iff]
    intro q
    rw [AEDisjoint.iUnion_right_iff]
    intro q'
    rw [key, key]
    apply hs.aedisjoint
    intro heq
    apply hgg'
    have h1 : (ρ q')⁻¹ * ρ q = (ι g')⁻¹ * ι g := by
      calc (ρ q')⁻¹ * ρ q = (ι g')⁻¹ * (ι g' * (ρ q')⁻¹) * ρ q := by group
        _ = (ι g')⁻¹ * (ι g * (ρ q)⁻¹) * ρ q := by rw [heq]
        _ = (ι g')⁻¹ * ι g := by group
    have h2 : (ι g')⁻¹ * ι g ∈ H := by
      rw [Subgroup.mem_subgroupOf]
      simpa [ι] using Γ₀.mul_mem (Γ₀.inv_mem g'.2) g.2
    have h3 : q' = q := by
      rw [← hout q', ← hout q]
      exact QuotientGroup.eq.mpr (h1 ▸ h2)
    subst h3
    have h4 : ι g = ι g' := mul_right_cancel heq
    have h5 : ((ι g : Γ) : G) = ((ι g' : Γ) : G) := by rw [h4]
    exact Subtype.ext h5
  · rw [measure_iUnion₀ hdisj (fun q => hs.nullMeasurableSet_smul _)]
    have hm : ∀ q, μ ((ρ q)⁻¹ • s) = μ s := fun q => by
      show μ (((ρ q)⁻¹ : Γ) • s) = μ s
      rw [show ((ρ q)⁻¹ : Γ) • s = (((ρ q)⁻¹ : Γ) : G) • s from rfl]
      exact measure_smul μ _ _
    simp only [hm, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [← Nat.card_eq_fintype_card]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cmp
