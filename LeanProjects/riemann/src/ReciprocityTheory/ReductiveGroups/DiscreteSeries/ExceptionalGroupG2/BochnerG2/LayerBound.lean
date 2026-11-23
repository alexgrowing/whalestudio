import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section LayerBound

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem khw_layer_succ_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) (k : ℕ) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ layer ε E V (k + 1)) (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0)
    (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) :
    IsNCSum ε (k + 1) (μ - lowK ε lam) ∧
      casValK ε (lowK ε lam) + 2 * ((k : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨hVfd, hVk, -, -⟩ := id hV
  obtain ⟨P, hP, hP0, hPμ, hPperp⟩ := lift_layer hE hU hVfd hVk hw hperp hμ hw0
  refine ⟨khw_big_weight hE hV hP hP0 hPμ, ?_⟩
  have hposition : ∀ i κ, slice i κ P ∈ Wp ε E V := fun i =>
    position_perp hE hU hV hmono hh hbig i hP
      (fun F hF hFs => hPperp F hF (phi_Wm_position hE hU hV hc hmono hh hbig i hF hFs))
  have hb := bochner_ineq hE hU hV hmono hh hbig hP hposition
  have hcas := casimirK_khwVec ε (bAct_isGlRep hE (k + 1)) hPμ
  rw [hcas, inner_smul_left, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal,
    ← RCLike.ofReal_pow, RCLike.re_mul_ofReal] at hb
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at hb
  change _ ≤ casValK ε μ * ‖P‖ ^ 2 at hb
  have hpos : 0 < ‖P‖ ^ 2 := pow_pos (norm_pos_iff.2 hP0) 2
  push_cast at hb
  exact le_of_mul_le_mul_right hb hpos

end LayerBound

end ReciprocityTheory.ChartRestriction.DS.G2
