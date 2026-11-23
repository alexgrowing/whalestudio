import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpCapLOfOf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_family_apply_holds : WFamApp := by
  intro d α L F c v x
  simp [wfam, WOp.app, List.map_append, List.sum_append, vfW, Function.comp_def]

theorem word_family_symbol_holds : WFamSymb := by
  intro d α L F c j x ξ τ hj hτ
  have h0 : ¬ (0 = j) := by omega
  simp only [wfam, WOp.symb, List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_nil, h0, if_false, add_zero]
  congr 1
  refine List.map_congr_left (fun t ht => ?_)
  simp only [Function.comp_apply, List.length_map]
  split_ifs with hl
  · congr 1
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left (fun X hX => hτ t ht X hX))
  · rfl

theorem trace_real_lie_holds : TrRealLie := by
  intro k r A X hA hX
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose k r
  have hH2 : Hpk k r * Hpk k r = 1 := WeylGroupFacts.hpk_sq
  have eA : Aᴴ = -(Hpk k r * A * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hA
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have eX : Xᴴ = -(Hpk k r * X * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hX
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have hstar : star (Matrix.trace (A * X)) = Matrix.trace (A * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, eX, eA, neg_mul_neg]
    calc Matrix.trace (Hpk k r * X * Hpk k r * (Hpk k r * A * Hpk k r))
        = Matrix.trace (Hpk k r * (X * (Hpk k r * Hpk k r) * A * Hpk k r)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * (Hpk k r * Hpk k r) * A * Hpk k r) * Hpk k r) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * A) := by simp only [Matrix.mul_assoc, hH2, Matrix.mul_one]
      _ = Matrix.trace (A * X) := Matrix.trace_mul_comm _ _
  exact Complex.conj_eq_iff_re.mp hstar

theorem smooth_on_levels_holds : CkLevOn := by
  intro k r m Dm E _ _ f hf g₀ hg₀
  have hg₀' : g₀ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hg₀.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg₀.2⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀'
  exact ⟨U, F, hU, hgU, by exact_mod_cast hF, fun g hg hgG => hfF g hg ⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩

theorem operator_capelli_vector : OpCVOf := opCVOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_right_capelli : OpCapROf := opCapROf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_left_capelli : OpCapLOf := opCapLOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
