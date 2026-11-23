import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sEmb : SEmb E := by
  intro r τ G x y
  simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem sMajFlag : SMajFlag E := by
  intro r X x x' hx hx' h
  exact (((orthonormalFlagTranslate_holds (E := E)) r X).2.2 x hx x' hx' h).2

theorem majorant_chart_of_normControl (h : OrthonormalChartNormControl (E := E)) : SMajXZ E := by
  intro r X x hx ho ρ hρ hρ1 Z hZ τ v
  exact ((h r X x hx ho ρ hρ hρ1).1 Z hZ).2.2 τ v

theorem sCmp_of (hm : SMajXZ E) : SCmp E := by
  intro r X x0 hx0 ho ρ' h1 h2 Z1 hZ1 z hz hsf τ v
  have hdom : X.xZ x0 Z1 ∈ X.dom := OrthonormalChartBounds.xZ_mem_dom X hx0 ho (by linarith)
  rw [sMajFlag r X z _ hz hdom hsf]
  exact hm r X x0 hx0 ho ρ' h1 h2 Z1 hZ1 τ v

theorem sFlagMap : SFlagMap E := by
  intro r X x y n h τ
  have hcol : ∀ (z : Frame X.Ψ r) (a : Fin r),
      col (mat (X.lmulC n z) τ) a = (n τ).mulVec (col (mat z τ) a) := by
    intro z a
    funext k
    simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  simp only [hcol]
  have hr : ∀ z : Frame X.Ψ r, (Set.range fun a : Fin X.p0 =>
      (n τ).mulVec (col (mat z τ) (Fin.castLE X.p0_le a))) =
      (Matrix.mulVecLin (n τ)) '' Set.range (fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) :=
    fun z => by rw [← Set.range_comp]; rfl
  rw [hr, hr, Submodule.span_image, Submodule.span_image, h τ]

theorem radius_pos_le_tenth : RadiusPosLeTenth := by
  intro c1 w hc1 hw
  unfold d6rh
  have hπ := Real.pi_gt_three
  have hpos : 0 < 12 * Real.pi * (c1 + w) := by positivity
  refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) ?_⟩
  nlinarith

theorem kato_norm_relation_tame_prime : KatoClassHeckeEulerFactorRelation := by
  intro r f d rd NA NC ep t hd hrd hNA hep ht ht1
  unfold frameIndexBound
  have hP0 : 0 ≤ (f : ℝ) * ((2 * f * (r - 2) : ℕ) : ℝ) ^ 3 * d * NA :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 3)) hd) hNA
  have hS : Real.sqrt (NC ^ 2 * rd / (t * ep)) = Real.sqrt (NC ^ 2 * rd / ep) / Real.sqrt t := by
    rw [← Real.sqrt_div' _ ht.le, div_div, mul_comm ep t]
  have htt : t ≤ Real.sqrt t := by
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht.le).symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, mul_nonneg hP0 (Real.sqrt_nonneg _)⟩
  rw [hS]
  exact le_trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) ht htt) hP0) (le_of_eq (mul_div_assoc _ _ _).symm)

theorem final_numerical_inequalities : UnipotentMoveNumericalInequalities := by
  intro ρ κ hρ hρ1 hκ0 hκ
  set s := ρ / 100 with hs
  set q := (1 - s) / (1 + s) with hqdef
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 / 1000 := by rw [hs]; linarith
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hq : 998 / 1000 ≤ q := by
    rw [hqdef, le_div_iff₀ (by linarith)]
    linarith
  have hκ' : κ ≤ ρ / 998 :=
    le_trans hκ (div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith))
  have ha : 3 * κ / q * (1 + s) ≤ ρ / 300 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hq0 (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hκ' (by linarith : (0 : ℝ) ≤ 1 + s),
      mul_le_mul_of_nonneg_left hq hρ.le]
  have ha0 : 0 ≤ 3 * κ / q * (1 + s) :=
    mul_nonneg (div_nonneg (by linarith) hq0.le) (by linarith)
  have ha1 : 3 * κ / q * (1 + s) ≤ 1 / 3000 := by linarith
  refine ⟨by linarith, by linarith, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left ha1 hρ.le]

theorem fdeg_pos : 0 < fdeg E := by
  have h := NumberField.IsTotallyComplex.finrank E
  have hp : 0 < Module.finrank ℚ E := Module.finrank_pos
  unfold fdeg
  rw [h] at hp ⊢
  omega

private lemma add_log_add_pos_of_one_le (w f K : ℝ) (hw : 1 ≤ w) (hf : 1 ≤ f) (hK : 1 ≤ K) :
    0 < w + 4 * f * Real.log (2 * K * (4 * f)) + 4 * f + 2 := by
  have hl : 0 ≤ Real.log (2 * K * (4 * f)) := Real.log_nonneg (by nlinarith)
  nlinarith

theorem epsilonZero_pos : EpsilonZeroPos E := by
  intro r X c1 w hc1 hw
  have hf : (1 : ℝ) ≤ fdeg E := by exact_mod_cast fdeg_pos
  have hd : 0 < dE E := by
    unfold dE
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  have hg : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  dsimp only [flowEpsilonBound]
  refine lt_min one_pos (div_pos (pow_pos (by linarith) 2) ?_)
  refine mul_pos (mul_pos (mul_pos (pow_pos (mul_pos hg (pow_pos hd 2)) 2) (pow_pos hNC 2)) hc1) ?_
  exact add_log_add_pos_of_one_le w _ _ hw hf (le_add_of_nonneg_right (mul_nonneg (by positivity) (by linarith)))

end

end UnipMove
