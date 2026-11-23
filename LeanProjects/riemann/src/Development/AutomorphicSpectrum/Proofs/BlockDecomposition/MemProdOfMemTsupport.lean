import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSectionStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.FinPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  have ht := ThBasic.continuous_thL hU n w
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = id := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id
  · have e : nrmL n w = fun y => y * thL n w y := funext fun y => by simp [nrmL, thL, hs]
    rw [e]
    exact continuous_id.mul ht

theorem isClosed_KGL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsClosed (GlobalTheory.LFun.KGL w n : Set (GLw n w)) :=
  (ThBasic.twist_basic E hU n w).2.2.2.2.2.1.isClosed

theorem nrmL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) {y : GLw n w} (hy : y ∈ GlobalTheory.LFun.KGL w n) :
    nrmL n w y ∈ GlobalTheory.LFun.KGL w n := by
  have ht := ThBasic.thL_mem_KGL hU n w y hy
  unfold nrmL
  unfold thL at ht
  split_ifs at ht ⊢ with hs
  · exact hy
  · exact mul_mem hy ht

theorem mem_prod_of_mem_tsupport (hU : Unr E) (a b : ℕ) (w : Pl E) {y : GLw a w × GLw b w}
    (hy : y ∈ tsupport ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : Set (GLw a w × GLw b w)).indicator
      (1 : GLw a w × GLw b w → ℂ))) :
    y.1 ∈ GlobalTheory.LFun.KGL w a ∧ y.2 ∈ GlobalTheory.LFun.KGL w b := by
  have hcl : IsClosed (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (isClosed_KGL hU a w).prod (isClosed_KGL hU b w)
  have h := closure_minimal Set.support_indicator_subset hcl hy
  exact Subgroup.mem_prod.1 h

theorem finite_pairs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S → ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w, HasCompactSupport (φ w)) → (∀ᶠ w in cofinite, φ w = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : Set (GLw a w × GLw b w)).indicator 1) → {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL b w y.2).val.charpoly = atPl w p.2}.Finite := by
  intro E _ _ _ hU a b S hS φ hc hφ
  let C₁ : ∀ w : Pl E, Set (GLw a w) := fun w => nrmL a w '' (Prod.fst '' tsupport (φ w))
  let C₂ : ∀ w : Pl E, Set (GLw b w) := fun w => nrmL b w '' (Prod.snd '' tsupport (φ w))
  have hC₁ : ∀ w, IsCompact (C₁ w) := fun w =>
    ((hc w).isCompact.image continuous_fst).image (continuous_nrmL hU a w)
  have hC₂ : ∀ w, IsCompact (C₂ w) := fun w =>
    ((hc w).isCompact.image continuous_snd).image (continuous_nrmL hU b w)
  have hK₁ : ∀ᶠ w in cofinite, C₁ w ⊆ GlobalTheory.LFun.KGL w a := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU a w (mem_prod_of_mem_tsupport hU a b w hy).1
  have hK₂ : ∀ᶠ w in cofinite, C₂ w ⊆ GlobalTheory.LFun.KGL w b := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU b w (mem_prod_of_mem_tsupport hU a b w hy).2
  refine ((GlobalTheory.T.finite_ellipticCharpoly_compact_section E a S hS C₁ hC₁ hK₁).prod (GlobalTheory.T.finite_ellipticCharpoly_compact_section E b S hS C₂ hC₂ hK₂)).subset ?_
  rintro p ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := h w hw
    exact ⟨_, ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := h w hw
    exact ⟨_, ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₂⟩

end GlobalTheory.CompanionTheory.FinPol
