import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_chart_noeth_frac

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

theorem ratio_eq [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) (k : K) (i : ι k) :
    mseg x (Function.update c k i) / mseg x c = x ⟨k, i⟩ / x ⟨k, c k⟩ := by
  have h1 : mseg x (Function.update c k i) = x ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : mseg x c = x ⟨k, c k⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  rw [h2] at hc
  rw [h1, h2, mul_div_mul_right _ _ (right_ne_zero_of_mul hc)]

theorem mseg_join {K' : Type} [Fintype K'] {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) c = mseg x (restrictChart c) * mseg z (fun k => c (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

def comb {K' : Type} {ι' : K' → Type} (t : ∀ k, ι k) (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => c (.inr k)

variable [∀ k, Fintype (ι k)]

theorem fnField_le [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hm : ∀ k (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
    intro k i
    rw [← ratio_eq x c hc k i]
    exact Subfield.subset_closure (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _)
  unfold fnField
  rw [Subfield.closure_le]
  rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have h : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hk k)]
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [h]
    exact div_mem (hm k i) (hm k j)

theorem isFractionRing_of_closure (R : Subalgebra O Ω) (h : Subfield.closure (R : Set Ω) = ⊤) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun z => ?_
  have hz : z ∈ Subfield.closure (R : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have e : Subring.closure (R : Set Ω) = R.toSubring := Subring.closure_eq R.toSubring
  rw [e] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

end PositivityTheory.Xgn.A_chart_noeth_frac

open PositivityTheory.Xgn.A_chart_noeth_frac in
theorem PositivityTheory.Xgn.t_chart_noeth_frac : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩), fun h c hc => ?_,
    fun K' _ _ ι' _ z => ⟨fun h => ?_, fun c hc => ?_⟩⟩
  · exact isFractionRing_of_closure _ (top_le_iff.1 (h ▸ fnField_le x c hc))
  · rw [eq_top_iff, ← h]
    unfold fnField
    refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨.inl k, i, j⟩, rfl⟩
  · have hc' := hc
    rw [mseg_join] at hc'
    refine ⟨left_ne_zero_of_mul hc', ?_⟩
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : mseg x t / mseg x (restrictChart c) =
        mseg (joinCoord x z) (comb t c) / mseg (joinCoord x z) c := by
      rw [mseg_join x z (comb t c), mseg_join x z c]
      exact (mul_div_mul_right _ _ (right_ne_zero_of_mul hc')).symm
    simp only
    rw [h]
    exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
