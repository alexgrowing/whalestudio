import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ k, u k ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by simp [avg, hc])

theorem exists_ne_zero_of_twOrb_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) : ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem exists_ne_zero_of_clSum_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (S : Set G) (wt f : G → ℂ) (h : clSum θ K S wt f ≠ 0) : ∃ δ ∈ S, ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  apply h
  unfold clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hS
  · by_contra hne
    exact hc ⟨c.rep, hS, exists_ne_zero_of_twOrb_ne_zero θ K c.rep f (right_ne_zero_of_mul hne)⟩
  · rfl

theorem nrmL_twConj {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ x : GLw n w) :
    nrmL n w (x⁻¹ * δ * thL n w x) = x⁻¹ * nrmL n w δ * x := by
  have hinv := TwistInvol.thL_involutive E n w x
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp
  · simp only [map_mul, map_inv, hinv]
    group

theorem exists_support_of_stTw_ne_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (Q : (w.adicCompletion E)[X]) (φ : GLw n w → ℂ) (h : stTw n w Q φ ≠ 0) :
    ∃ y, φ y ≠ 0 ∧ (nrmL n w y).val.charpoly = Q := by
  obtain ⟨δ, hδ, x, hx⟩ := exists_ne_zero_of_clSum_ne_zero _ _ _ _ _ h
  refine ⟨_, hx, ?_⟩
  rw [nrmL_twConj, ← (show (nrmL n w δ).val.charpoly = Q from hδ), Units.val_mul, Matrix.charpoly_mul_comm,
    ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.BCT
