import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open Ad3 Ad3.S
open GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)

namespace GlobalTheory.CompanionTheory.AdjointLift

theorem localChar_inv (c : HeckeCharacter ℚ) (v : Pl) :
    localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext a
  rfl

theorem admissible_character_inv {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl} (h : admitted D c δ S) :
    admitted D c⁻¹ δ S where
  fin := h.fin.inv
  sgn w := by
    have e : (((c⁻¹).infiniteComponent w (-1) : Circle) : ℂ) =
        (((c.infiniteComponent w (-1))⁻¹ : Circle) : ℂ) := rfl
    rw [e, Circle.coe_inv, h.sgn w]
    split_ifs <;> simp
  bad := h.bad
  unr v hv := by
    rw [localChar_inv]
    exact isUnramifiedChar_inv_iff.2 (h.unr v hv)

theorem cont_zero {D : Dat} {c : HeckeCharacter ℚ} {S : Finset Pl} {Λ : ℂ → ℂ}
    (h : Cont D c S 1 Λ) (h1 : Λ 1 = 0) : Cont D c S 0 (dslope Λ 1) := by
  obtain ⟨hd, ho, he⟩ := h
  have hopen : IsOpen {s : ℂ | 1 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 1 / 4 < s.re} ∈ nhds (1 : ℂ) := hopen.mem_nhds (by norm_num)
  have hd0 := (Complex.differentiableOn_dslope hmem).2 hd
  have hmul : ∀ s : ℂ, (s - 1) * dslope Λ 1 s = Λ s := fun s => by
    simpa [h1] using sub_smul_dslope Λ 1 s
  refine ⟨hd0, ?_, ?_⟩
  · intro b
    obtain ⟨C, hC⟩ := ho b
    have hsub : Metric.closedBall (1 : ℂ) (1 / 2) ⊆ {s : ℂ | 1 / 4 < s.re} := by
      intro s hs
      have h2 : ‖s - 1‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hs
      have h3 := (abs_le.1 ((Complex.abs_re_le_norm (s - 1)).trans h2)).1
      simp only [Complex.sub_re, Complex.one_re] at h3
      simp only [Set.mem_setOf_eq]
      linarith
    obtain ⟨K, hK⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      (hd0.continuousOn.mono hsub)
    refine ⟨2 * |C| + |K|, fun s hs1 hs2 => ?_⟩
    have hC0 : 0 ≤ |C| := abs_nonneg C
    have hK0 : 0 ≤ |K| := abs_nonneg K
    have hE : 1 ≤ Real.exp ((2 * |C| + |K|) * s.im ^ 2) :=
      Real.one_le_exp (by positivity)
    by_cases hs : ‖s - 1‖ ≤ 1 / 2
    · have hb : ‖dslope Λ 1 s‖ ≤ K := hK s (by simpa [dist_eq_norm] using hs)
      have hb2 : K ≤ 2 * |C| + |K| := (le_abs_self K).trans (by linarith)
      exact (hb.trans hb2).trans (le_mul_of_one_le_right (by positivity) hE)
    · push_neg at hs
      have hn : ‖s - 1‖ * ‖dslope Λ 1 s‖ = ‖Λ s‖ := by rw [← norm_mul, hmul]
      have hb := hC s hs1 hs2
      have hexp : Real.exp (C * s.im ^ 2) ≤ Real.exp ((2 * |C| + |K|) * s.im ^ 2) := by
        apply Real.exp_le_exp.2
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have := le_abs_self C
        linarith
      have hb2 : ‖Λ s‖ ≤ |C| * Real.exp ((2 * |C| + |K|) * s.im ^ 2) :=
        hb.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_left hexp hC0))
      have hh : 1 / 2 * ‖dslope Λ 1 s‖ ≤ ‖Λ s‖ := by
        rw [← hn]
        exact mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
      have hpos := Real.exp_pos ((2 * |C| + |K|) * s.im ^ 2)
      have : |K| * Real.exp ((2 * |C| + |K|) * s.im ^ 2) ≥ 0 := by positivity
      nlinarith
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      intro h0
      have : s = 1 := sub_eq_zero.1 h0
      rw [this] at hs
      simp at hs
    apply mul_left_cancel₀ hne
    rw [hmul, he s hs]
    ring

theorem anOf : AnOf := by
  intro a D hFE hEx
  by_cases hd : Dih a
  · exact Or.inl hd
  refine Or.inr fun c δ S hA => ?_
  have hA' := admissible_character_inv hA
  obtain ⟨Λ, hΛ⟩ := hEx c δ S hA
  obtain ⟨Λ', hΛ'⟩ := hEx c⁻¹ δ S hA'
  obtain ⟨hfe, h1⟩ := hFE c δ S hA Λ Λ' hΛ hΛ'
  obtain ⟨-, h1'⟩ := hFE c⁻¹ δ S hA' Λ' Λ hΛ' (by rwa [inv_inv])
  have h1 := h1.resolve_left hd
  have h1' := h1'.resolve_left hd
  refine ⟨dslope Λ 1, dslope Λ' 1, cont_zero hΛ h1, cont_zero hΛ' h1', fun s hs1 hs2 => ?_⟩
  have e := hfe s hs1 hs2
  have e1 : Λ s = (s - 1) * dslope Λ 1 s := by
    simpa [h1] using (sub_smul_dslope Λ 1 s).symm
  have e2 : Λ' (1 - s) = -s * dslope Λ' 1 (1 - s) := by
    simpa [h1'] using (sub_smul_dslope Λ' 1 (1 - s)).symm
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs1
  have hs1' : s - 1 ≠ 0 := by
    intro h0
    have : s = 1 := sub_eq_zero.1 h0
    rw [this] at hs2
    norm_num at hs2
  rw [e1, e2] at e
  apply mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.2 hs0) hs1')
  linear_combination e

end GlobalTheory.CompanionTheory.AdjointLift

end
