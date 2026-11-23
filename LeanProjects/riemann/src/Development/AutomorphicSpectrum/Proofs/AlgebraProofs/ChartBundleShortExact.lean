import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

theorem chartRing_le (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t, rfl⟩
  have h : mseg x t / mseg x (restrictChart s) =
      mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s := by
    rw [mseg_join x z (comb t s), mseg_join x z s]
    exact (mul_div_mul_right _ _ hw).symm
  have h2 := div_mem_chartRing (o := O) (mseg (joinCoord x z)) s (comb t s)
  rw [← h] at h2
  exact h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ N₂ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (E : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂) (E₁ : ChartBundle O (mseg x) N₁ V₁) (E₂ : ChartBundle O (mseg x) N₂ V₂), IsSubQuot O x E i p E₁ E₂ → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V) (EB₁ : ChartBundle O (mseg (joinCoord x z)) N₁ V₁) (EB₂ : ChartBundle O (mseg (joinCoord x z)) N₂ V₂), IsPull O x z E EB → IsPull O x z E₁ EB₁ → IsPull O x z E₂ EB₂ → IsSubQuot O (joinCoord x z) EB i p EB₁ EB₂ := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N N₁ N₂ V _ _ V₁ _ _ V₂ _ _ E i p E₁ E₂ h K' _ _ ι' _ z EB EB₁ EB₂ hE hE₁ hE₂
  obtain ⟨hi, hp, hex, hc⟩ := h
  refine ⟨hi, hp, hex, fun s hs => ?_⟩
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    exact left_ne_zero_of_mul hs
  obtain ⟨h₁, h₂⟩ := hc _ hx
  have hF : LocFree (chartRing O (mseg x) (restrictChart s)) N₂
      ((E.lat (restrictChart s)).map p.toAddMonoidHom) := by
    rw [← h₂]
    exact ⟨fun a ha v hv => E₂.stable _ a ha v hv, E₂.frame _ hx⟩
  obtain ⟨c₁, c₂⟩ := SpanExact.span_comap_exact _ _ (chartRing_le x z s hs) i p hi hex
    (E.lat (restrictChart s)) N₂ (fun a ha v hv => E.stable _ a ha v hv) hF
  have e : EB.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E.lat (restrictChart s) : Set V) := hE s hs
  have e₁ : EB₁.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E₁.lat (restrictChart s) : Set V₁) := hE₁ s hs
  have e₂ : EB₂.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E₂.lat (restrictChart s) : Set V₂) := hE₂ s hs
  rw [e, e₁, e₂, h₁, h₂]
  exact ⟨c₁.symm, c₂.symm⟩

end GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot
