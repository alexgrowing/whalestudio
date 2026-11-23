import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpSlotBound

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Boch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem bochner_ineq (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hposition : ∀ i κ, slice i κ P ∈ Wp ε E V) :
    (casValK ε (lowK ε lam) + 2 * (k : ℝ) * (h - n + 1)) * ‖P‖ ^ 2 ≤
      RCLike.re (inner ℂ (casimirK ε (bAct E k) P) P) := by
  have hc : casimirK ε (mAct E k) P = (casValK ε (lowK ε lam) : ℂ) • P := by
    ext κ
    rw [casimirK_mAct_apply, PiLp.smul_apply]
    apply casimirK_irr hE hV
    have h1 := (Submodule.mem_iInf _).1 hP κ
    rw [Submodule.mem_comap] at h1
    split_ifs at h1 with h2
    · simpa [coord] using h1
    · have h3 : coord k κ P = 0 := (Submodule.mem_bot ℂ).1 h1
      have h4 : P κ = 0 := by simpa [coord] using h3
      rw [h4]; exact V.zero_mem
  have hpositions : ∀ i : Fin k, 2 * (h - n + 1) * ‖P‖ ^ 2 ≤
      2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := fun i =>
    crossOp_position_bound hE hU hV hmono hh hbig i (fun κ => hposition i κ)
  have hnn := factorCasimir_nonneg (M := M) (ε := ε) k P
  have key : RCLike.re (inner ℂ (casimirK ε (bAct E k) P) P) =
      RCLike.re (inner ℂ (factorCasimir (M := M) ε k P) P) + casValK ε (lowK ε lam) * ‖P‖ ^ 2 +
        ∑ i, 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
    rw [casimirK_bAct (ε := ε) (E := E) k]
    simp only [LinearMap.add_apply, hc, inner_add_left, two_nsmul,
      inner_smul_left, map_add, inner_self_eq_norm_sq_to_K]
    simp [Complex.conj_ofReal]
    rw [sum_inner, Complex.re_sum, ← Finset.sum_add_distrib]
    norm_cast
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∑ _i : Fin k, 2 * (h - n + 1) * ‖P‖ ^ 2 ≤
      ∑ i, 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := Finset.sum_le_sum fun i _ => hpositions i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [key]
  nlinarith [hsum, hnn]

end Boch

end ReciprocityTheory.ChartRestriction.DS
