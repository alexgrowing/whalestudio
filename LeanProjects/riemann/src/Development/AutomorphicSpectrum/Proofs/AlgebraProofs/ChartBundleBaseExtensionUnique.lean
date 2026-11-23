import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraRest
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullPreserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

section Closure

variable {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]

theorem const_smul_mem (R : Subalgebra O Ω) (A : AddSubgroup V) (c : O) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    exact AddSubgroup.subset_closure
      ⟨algebraMap O Ω c * a, mul_mem (R.algebraMap_mem c) ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem exists_const_smul_mem [IsDomain O] (R : Subalgebra O Ω) (A B : AddSubgroup V)
    (h : ∀ v ∈ A, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁, m₁⟩ := h₁
    obtain ⟨c₂, hc₂, m₂⟩ := h₂
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
    have e : algebraMap O Ω (c₁ * c₂) • (w₁ + w₂) =
        algebraMap O Ω c₂ • (algebraMap O Ω c₁ • w₁) +
          algebraMap O Ω c₁ • (algebraMap O Ω c₂ • w₂) := by
      rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm]
    rw [e]
    exact add_mem (const_smul_mem R B c₂ m₁) (const_smul_mem R B c₁ m₂)
  | neg w _ h =>
    obtain ⟨c, hc, m⟩ := h
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem m⟩

theorem mem_span_scaled (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ B ↔ ∃ e ∈ A, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e :=
  _root_.UpperTheory.Reformulated.B.Ydb6.main R A B c h v

end Closure

theorem pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hE hE'
  have hx : ∀ s, mseg (joinCoord x z) s ≠ 0 → mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    apply hs
    have e : mseg (joinCoord x z) s =
        mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
      simp only [mseg, Fintype.prod_sum_type]
      rfl
    rw [e, h, zero_mul]
  refine ⟨fun h s hs => ?_, fun h s hs => ⟨fun v hv => ?_, fun v hv => ?_⟩,
    fun c h s hs v => ?_⟩
  · rw [hE s hs, hE' s hs]
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, h _ (hx s hs) he, rfl⟩
  · rw [hE s hs] at hv
    rw [hE' s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).1 hv
  · rw [hE' s hs] at hv
    rw [hE s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).2 hv
  · rw [hE s hs, hE' s hs]
    exact mem_span_scaled _ _ _ c (h _ (hx s hs)) v

end GlobalTheory.CompanionTheory.Ar.Num.PullPreserve
