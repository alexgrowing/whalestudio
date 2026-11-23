import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open Finset
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chamber

theorem rt_inner_wt_chain : ∀ {k : ℕ} {P S : Finset (SV k)}, IsPar P → S ⊆ P →
    (∀ u ∈ P \ S, ∀ v ∈ P \ S, u ≠ v → ⟪rt P u, wt S v⟫_ℝ = 0) ∧ ∀ u ∈ P \ S, 0 < ⟪rt P u, wt S u⟫_ℝ := by
  intro k P S hP hS
  have orth : ∀ u : SV k, ∀ x ∈ aP (P.erase u), ⟪rt P u, x⟫_ℝ = 0 := fun u x hx => by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := aP (P.erase u)) (vec u)
    rw [Submodule.mem_orthogonal] at h
    rw [real_inner_comm]
    exact h x hx
  have sub : ∀ u, u ∉ S → S ⊆ P.erase u := fun u hu w hw =>
    mem_erase.2 ⟨fun e => hu (e ▸ hw), hS hw⟩
  have prmem : ∀ u, u ∉ S → ∀ x, pr S x ∈ aP (P.erase u) := fun u hu x =>
    vecSpan_mono (sub u hu) (Submodule.starProjection_apply_mem _ _)
  refine ⟨fun u hu v hv huv => ?_, fun u hu => ?_⟩
  · have hvm : vec v ∈ aP (P.erase u) :=
      Submodule.subset_span ⟨v, mem_erase.2 ⟨Ne.symm huv, (mem_sdiff.1 hv).1⟩, rfl⟩
    exact orth u _ (sub_mem hvm (prmem u (mem_sdiff.1 hu).2 _))
  · have h1 : ⟪rt P u, wt S u⟫_ℝ = ⟪rt P u, vec u⟫_ℝ := by
      rw [wt, inner_sub_right, orth u _ (prmem u (mem_sdiff.1 hu).2 _), sub_zero]
    have h2 : ⟪rt P u, rt P u⟫_ℝ = ⟪rt P u, vec u⟫_ℝ := by
      have e : rt P u = vec u - pr (P.erase u) (vec u) := rfl
      have hm : pr (P.erase u) (vec u) ∈ aP (P.erase u) := Submodule.starProjection_apply_mem _ _
      nth_rewrite 2 [e]
      rw [inner_sub_right, orth u _ hm, sub_zero]
    rw [h1, ← h2]
    exact real_inner_self_pos.2 (hP.wt_ne_zero (erase_subset u P)
      (mem_sdiff.2 ⟨(mem_sdiff.1 hu).1, fun h => (notMem_erase u P) h⟩))

example : ∀ {k : ℕ} {P S : Finset (SV k)}, IsPar P → S ⊆ P →
    (∀ u ∈ P \ S, ∀ v ∈ P \ S, u ≠ v → ⟪rt P u, wt S v⟫_ℝ = 0) ∧ ∀ u ∈ P \ S, 0 < ⟪rt P u, wt S u⟫_ℝ := @rt_inner_wt_chain

end GlobalTheory.Chamber
