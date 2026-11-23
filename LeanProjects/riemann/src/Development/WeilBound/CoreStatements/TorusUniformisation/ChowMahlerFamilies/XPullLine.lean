import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_line
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord (fun p => φ (x p)) z) s =
      φ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type, map_prod]
  rfl

theorem chartMon_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) :
    chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a) =
      φ (chartMon x (restrictChart s) a) := by
  simp only [chartMon, Fintype.prod_sum_type, pullDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zpow_zero, Finset.prod_const_one, mul_one, map_prod, map_zpow₀]
  rfl

theorem map_mem (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0)
    (r : Ω) (hr : r ∈ chartRing O (mseg x) (restrictChart s)) :
    φ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s).comap φ := by
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : φ (mseg x t / mseg x (restrictChart s)) =
        mseg (joinCoord (fun p => φ (x p)) z) (comb t s) / mseg (joinCoord (fun p => φ (x p)) z) s := by
      rw [mseg_join φ x z (comb t s), mseg_join φ x z s, map_div₀]
      exact (mul_div_mul_right _ _ hw).symm
    have h2 := div_mem_chartRing (o := O) (mseg (joinCoord (fun p => φ (x p)) z)) s (comb t s)
    rw [← h] at h2
    exact h2
  exact hle hr

theorem main [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (u : Ω) (a : K → ℤ)
    (A : (∀ k, ι k) → AddSubgroup Ω) (hA : IsLine O x u a A)
    (B : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup Ω₁)
    (hB : ∀ s, mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0 → B s = AddSubgroup.closure
      {v | ∃ c ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s, ∃ e ∈ A (restrictChart s),
        v = c • φ e}) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0) (v : Ω₁) :
    v ∈ B s ↔ ∃ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s,
      v = r * (φ u * chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a)) := by
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    intro h
    exact left_ne_zero_of_mul hs (by rw [h, map_zero])
  rw [hB s hs, chartMon_join, ← map_mul]
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      obtain ⟨r, hr, rfl⟩ := (hA _ hx e).1 he
      refine ⟨c * φ r, mul_mem hc (map_mem φ x z s hs r hr), ?_⟩
      rw [smul_eq_mul, map_mul, mul_assoc]
    | zero => exact ⟨0, zero_mem _, by rw [zero_mul]⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨r₁, hr₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, rfl⟩ := h₂
      exact ⟨r₁ + r₂, add_mem hr₁ hr₂, by rw [add_mul]⟩
    | neg w _ h =>
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨-r, neg_mem hr, by rw [neg_mul]⟩
  · rintro ⟨r, hr, rfl⟩
    exact AddSubgroup.subset_closure ⟨r, hr, _, (hA _ hx _).2 ⟨1, one_mem _, (one_mul _).symm⟩, rfl⟩

end PositivityTheory.Xgn.A_pull_line
