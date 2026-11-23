import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Boch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem bochner_ineq (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hposition : ∀ i κ, slice i κ P ∈ Wp ε E V) :
    (casValK ε (lowK ε lam) + 2 * (k : ℝ) * (h - n + 1)) * ‖P‖ ^ 2 ≤
      RCLike.re (inner ℂ (casimirK ε (bAct E k) P) P) := by
  classical

  have hP' := hP
  simp only [ReciprocityTheory.ChartRestriction.DS.ncV, Submodule.mem_iInf, Submodule.mem_comap] at hP'

  have hcas : casimirK ε (mAct E k) P = ((casValK ε (lowK ε lam) : ℝ) : ℂ) • P := by
    refine PiLp.ext fun κ => ?_
    rw [ReciprocityTheory.ChartRestriction.DS.casimirK_mAct_apply, PiLp.smul_apply]
    have hm := hP' κ
    by_cases hκ : ∀ i, ε (κ i).1 ≠ ε (κ i).2
    · rw [if_pos hκ] at hm
      have hm' : P κ ∈ V := hm
      exact ReciprocityTheory.ChartRestriction.DS.casimirK_irr hE hV _ hm'
    · rw [if_neg hκ] at hm
      have hz : P κ = 0 := (Submodule.mem_bot ℂ).1 hm
      rw [hz, map_zero, smul_zero]

  have hsplit : RCLike.re (inner ℂ (casimirK ε (bAct E k) P) P)
      = RCLike.re (inner ℂ (factorCasimir ε k P) P) + RCLike.re (inner ℂ (casimirK ε (mAct E k) P) P)
        + 2 * ∑ i, RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
    rw [ReciprocityTheory.ChartRestriction.DS.casimirK_bAct]
    simp only [two_nsmul, LinearMap.add_apply, LinearMap.sum_apply,
      inner_add_left, sum_inner, map_add, map_sum]
    ring
  have h1 : 0 ≤ RCLike.re (inner ℂ (factorCasimir ε k P) P) :=
    ReciprocityTheory.ChartRestriction.DS.factorCasimir_nonneg k P
  have h2 : RCLike.re (inner ℂ (casimirK ε (mAct E k) P) P) = casValK ε (lowK ε lam) * ‖P‖ ^ 2 := by
    rw [hcas, inner_smul_left, Complex.conj_ofReal, ← inner_self_eq_norm_sq (𝕜 := ℂ) P]
    simp [Complex.mul_re]

  have h3 : ∀ i : Fin k, 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) :=
    fun i => ReciprocityTheory.ChartRestriction.DS.G2.crossOp_position_bound hE hU hV hmono hh hbig i (fun κ => hposition i κ)
  have h4 : (k : ℝ) * (2 * (h - n + 1) * ‖P‖ ^ 2) ≤ ∑ i : Fin k, 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h3 i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  rw [hsplit, h2, ← Finset.mul_sum] at *
  nlinarith [h1, h4]

end Boch

end ReciprocityTheory.ChartRestriction.DS.G2
